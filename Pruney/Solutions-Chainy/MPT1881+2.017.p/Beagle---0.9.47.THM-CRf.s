%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:08 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 568 expanded)
%              Number of leaves         :   35 ( 207 expanded)
%              Depth                    :   13
%              Number of atoms          :  260 (1434 expanded)
%              Number of equality atoms :   32 ( 209 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_32,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_tops_1(B,A)
              & v2_tex_2(B,A) )
           => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3] : ~ v1_subset_1(k2_subset_1(A_3),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,(
    ! [A_3] : ~ v1_subset_1(A_3,A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_14,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_647,plain,(
    ! [A_107] :
      ( u1_struct_0(A_107) = k2_struct_0(A_107)
      | ~ l1_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_653,plain,(
    ! [A_109] :
      ( u1_struct_0(A_109) = k2_struct_0(A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_14,c_647])).

tff(c_657,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_653])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_661,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_44])).

tff(c_54,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_75,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_77,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_14,c_77])).

tff(c_86,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_82])).

tff(c_60,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_93,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_60])).

tff(c_94,plain,(
    ~ v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_93])).

tff(c_87,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_44])).

tff(c_118,plain,(
    ! [B_45,A_46] :
      ( v1_subset_1(B_45,A_46)
      | B_45 = A_46
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_121,plain,
    ( v1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_87,c_118])).

tff(c_130,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_121])).

tff(c_16,plain,(
    ! [A_8] :
      ( k2_pre_topc(A_8,k2_struct_0(A_8)) = k2_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_145,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_16])).

tff(c_149,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_130,c_145])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_139,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_86])).

tff(c_213,plain,(
    ! [B_56,A_57] :
      ( v1_tops_1(B_56,A_57)
      | k2_pre_topc(A_57,B_56) != u1_struct_0(A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_216,plain,(
    ! [B_56] :
      ( v1_tops_1(B_56,'#skF_2')
      | k2_pre_topc('#skF_2',B_56) != u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_56,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_213])).

tff(c_229,plain,(
    ! [B_58] :
      ( v1_tops_1(B_58,'#skF_2')
      | k2_pre_topc('#skF_2',B_58) != '#skF_3'
      | ~ m1_subset_1(B_58,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_139,c_216])).

tff(c_237,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_62,c_229])).

tff(c_241,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_237])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_48,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_283,plain,(
    ! [B_64,A_65] :
      ( v2_tex_2(B_64,A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v1_tdlat_3(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_286,plain,(
    ! [B_64] :
      ( v2_tex_2(B_64,'#skF_2')
      | ~ m1_subset_1(B_64,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_283])).

tff(c_296,plain,(
    ! [B_64] :
      ( v2_tex_2(B_64,'#skF_2')
      | ~ m1_subset_1(B_64,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_286])).

tff(c_300,plain,(
    ! [B_66] :
      ( v2_tex_2(B_66,'#skF_2')
      | ~ m1_subset_1(B_66,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_296])).

tff(c_310,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_300])).

tff(c_605,plain,(
    ! [B_104,A_105] :
      ( v3_tex_2(B_104,A_105)
      | ~ v2_tex_2(B_104,A_105)
      | ~ v1_tops_1(B_104,A_105)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_611,plain,(
    ! [B_104] :
      ( v3_tex_2(B_104,'#skF_2')
      | ~ v2_tex_2(B_104,'#skF_2')
      | ~ v1_tops_1(B_104,'#skF_2')
      | ~ m1_subset_1(B_104,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_605])).

tff(c_622,plain,(
    ! [B_104] :
      ( v3_tex_2(B_104,'#skF_2')
      | ~ v2_tex_2(B_104,'#skF_2')
      | ~ v1_tops_1(B_104,'#skF_2')
      | ~ m1_subset_1(B_104,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_611])).

tff(c_626,plain,(
    ! [B_106] :
      ( v3_tex_2(B_106,'#skF_2')
      | ~ v2_tex_2(B_106,'#skF_2')
      | ~ v1_tops_1(B_106,'#skF_2')
      | ~ m1_subset_1(B_106,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_622])).

tff(c_637,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_626])).

tff(c_642,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_310,c_637])).

tff(c_644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_642])).

tff(c_646,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_707,plain,(
    ! [B_118,A_119] :
      ( v2_tex_2(B_118,A_119)
      | ~ v3_tex_2(B_118,A_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_732,plain,(
    ! [A_122] :
      ( v2_tex_2(u1_struct_0(A_122),A_122)
      | ~ v3_tex_2(u1_struct_0(A_122),A_122)
      | ~ l1_pre_topc(A_122) ) ),
    inference(resolution,[status(thm)],[c_62,c_707])).

tff(c_735,plain,
    ( v2_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | ~ v3_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_732])).

tff(c_737,plain,
    ( v2_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_657,c_735])).

tff(c_738,plain,(
    ~ v3_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_737])).

tff(c_756,plain,(
    ! [B_124,A_125] :
      ( v1_tops_1(B_124,A_125)
      | k2_pre_topc(A_125,B_124) != u1_struct_0(A_125)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_763,plain,(
    ! [B_124] :
      ( v1_tops_1(B_124,'#skF_2')
      | k2_pre_topc('#skF_2',B_124) != u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_756])).

tff(c_795,plain,(
    ! [B_129] :
      ( v1_tops_1(B_129,'#skF_2')
      | k2_pre_topc('#skF_2',B_129) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_657,c_763])).

tff(c_809,plain,
    ( v1_tops_1(k2_struct_0('#skF_2'),'#skF_2')
    | k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) != k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_795])).

tff(c_811,plain,(
    k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_809])).

tff(c_814,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_811])).

tff(c_818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_814])).

tff(c_819,plain,(
    v1_tops_1(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_809])).

tff(c_936,plain,(
    ! [B_141,A_142] :
      ( v2_tex_2(B_141,A_142)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142)
      | ~ v1_tdlat_3(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_943,plain,(
    ! [B_141] :
      ( v2_tex_2(B_141,'#skF_2')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_936])).

tff(c_950,plain,(
    ! [B_141] :
      ( v2_tex_2(B_141,'#skF_2')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_943])).

tff(c_953,plain,(
    ! [B_143] :
      ( v2_tex_2(B_143,'#skF_2')
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_950])).

tff(c_968,plain,(
    v2_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_953])).

tff(c_1145,plain,(
    ! [B_165,A_166] :
      ( v3_tex_2(B_165,A_166)
      | ~ v2_tex_2(B_165,A_166)
      | ~ v1_tops_1(B_165,A_166)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1152,plain,(
    ! [B_165] :
      ( v3_tex_2(B_165,'#skF_2')
      | ~ v2_tex_2(B_165,'#skF_2')
      | ~ v1_tops_1(B_165,'#skF_2')
      | ~ m1_subset_1(B_165,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_1145])).

tff(c_1159,plain,(
    ! [B_165] :
      ( v3_tex_2(B_165,'#skF_2')
      | ~ v2_tex_2(B_165,'#skF_2')
      | ~ v1_tops_1(B_165,'#skF_2')
      | ~ m1_subset_1(B_165,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_1152])).

tff(c_1162,plain,(
    ! [B_167] :
      ( v3_tex_2(B_167,'#skF_2')
      | ~ v2_tex_2(B_167,'#skF_2')
      | ~ v1_tops_1(B_167,'#skF_2')
      | ~ m1_subset_1(B_167,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1159])).

tff(c_1173,plain,
    ( v3_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v2_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v1_tops_1(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_1162])).

tff(c_1180,plain,(
    v3_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_968,c_1173])).

tff(c_1182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_738,c_1180])).

tff(c_1183,plain,(
    v2_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_737])).

tff(c_667,plain,(
    ! [A_112,B_113] :
      ( r1_tarski(A_112,B_113)
      | ~ m1_subset_1(A_112,k1_zfmisc_1(B_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_678,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_661,c_667])).

tff(c_2385,plain,(
    ! [C_277,B_278,A_279] :
      ( C_277 = B_278
      | ~ r1_tarski(B_278,C_277)
      | ~ v2_tex_2(C_277,A_279)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ v3_tex_2(B_278,A_279)
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ l1_pre_topc(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2399,plain,(
    ! [A_279] :
      ( k2_struct_0('#skF_2') = '#skF_3'
      | ~ v2_tex_2(k2_struct_0('#skF_2'),A_279)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ v3_tex_2('#skF_3',A_279)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ l1_pre_topc(A_279) ) ),
    inference(resolution,[status(thm)],[c_678,c_2385])).

tff(c_2495,plain,(
    ! [A_287] :
      ( ~ v2_tex_2(k2_struct_0('#skF_2'),A_287)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ v3_tex_2('#skF_3',A_287)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ l1_pre_topc(A_287) ) ),
    inference(splitLeft,[status(thm)],[c_2399])).

tff(c_2501,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_2495])).

tff(c_2505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_661,c_657,c_646,c_62,c_1183,c_2501])).

tff(c_2506,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2399])).

tff(c_645,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_660,plain,(
    v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_645])).

tff(c_2532,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2506,c_660])).

tff(c_2540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_2532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:02:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.77  
% 4.45/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.77  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.45/1.77  
% 4.45/1.77  %Foreground sorts:
% 4.45/1.77  
% 4.45/1.77  
% 4.45/1.77  %Background operators:
% 4.45/1.77  
% 4.45/1.77  
% 4.45/1.77  %Foreground operators:
% 4.45/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.45/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.77  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.45/1.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.45/1.77  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.45/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.77  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.45/1.77  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.45/1.77  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.45/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.45/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.45/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.45/1.77  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.45/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.45/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.45/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.45/1.77  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.45/1.77  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.45/1.77  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.45/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.45/1.77  
% 4.45/1.79  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.45/1.79  tff(f_32, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 4.45/1.79  tff(f_136, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 4.45/1.79  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.45/1.79  tff(f_40, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.45/1.79  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 4.45/1.79  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 4.45/1.79  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.45/1.79  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 4.45/1.79  tff(f_102, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 4.45/1.79  tff(f_118, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 4.45/1.79  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 4.45/1.79  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.45/1.79  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.45/1.79  tff(c_6, plain, (![A_3]: (~v1_subset_1(k2_subset_1(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.45/1.79  tff(c_61, plain, (![A_3]: (~v1_subset_1(A_3, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 4.45/1.79  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.45/1.79  tff(c_14, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.45/1.79  tff(c_647, plain, (![A_107]: (u1_struct_0(A_107)=k2_struct_0(A_107) | ~l1_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.45/1.79  tff(c_653, plain, (![A_109]: (u1_struct_0(A_109)=k2_struct_0(A_109) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_14, c_647])).
% 4.45/1.79  tff(c_657, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_653])).
% 4.45/1.79  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.45/1.79  tff(c_661, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_657, c_44])).
% 4.45/1.79  tff(c_54, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.45/1.79  tff(c_75, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 4.45/1.79  tff(c_77, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.45/1.79  tff(c_82, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_14, c_77])).
% 4.45/1.79  tff(c_86, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_82])).
% 4.45/1.79  tff(c_60, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.45/1.79  tff(c_93, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_60])).
% 4.45/1.79  tff(c_94, plain, (~v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_75, c_93])).
% 4.45/1.79  tff(c_87, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_44])).
% 4.45/1.79  tff(c_118, plain, (![B_45, A_46]: (v1_subset_1(B_45, A_46) | B_45=A_46 | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.45/1.79  tff(c_121, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_87, c_118])).
% 4.45/1.79  tff(c_130, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_94, c_121])).
% 4.45/1.79  tff(c_16, plain, (![A_8]: (k2_pre_topc(A_8, k2_struct_0(A_8))=k2_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.45/1.79  tff(c_145, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_130, c_16])).
% 4.45/1.79  tff(c_149, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_130, c_145])).
% 4.45/1.79  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.45/1.79  tff(c_62, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.45/1.79  tff(c_139, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_86])).
% 4.45/1.79  tff(c_213, plain, (![B_56, A_57]: (v1_tops_1(B_56, A_57) | k2_pre_topc(A_57, B_56)!=u1_struct_0(A_57) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.45/1.79  tff(c_216, plain, (![B_56]: (v1_tops_1(B_56, '#skF_2') | k2_pre_topc('#skF_2', B_56)!=u1_struct_0('#skF_2') | ~m1_subset_1(B_56, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_213])).
% 4.45/1.79  tff(c_229, plain, (![B_58]: (v1_tops_1(B_58, '#skF_2') | k2_pre_topc('#skF_2', B_58)!='#skF_3' | ~m1_subset_1(B_58, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_139, c_216])).
% 4.45/1.79  tff(c_237, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_62, c_229])).
% 4.45/1.79  tff(c_241, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_237])).
% 4.45/1.79  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.45/1.79  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.45/1.79  tff(c_48, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.45/1.79  tff(c_283, plain, (![B_64, A_65]: (v2_tex_2(B_64, A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v1_tdlat_3(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.45/1.79  tff(c_286, plain, (![B_64]: (v2_tex_2(B_64, '#skF_2') | ~m1_subset_1(B_64, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_283])).
% 4.45/1.79  tff(c_296, plain, (![B_64]: (v2_tex_2(B_64, '#skF_2') | ~m1_subset_1(B_64, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_286])).
% 4.45/1.79  tff(c_300, plain, (![B_66]: (v2_tex_2(B_66, '#skF_2') | ~m1_subset_1(B_66, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_296])).
% 4.45/1.79  tff(c_310, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_300])).
% 4.45/1.79  tff(c_605, plain, (![B_104, A_105]: (v3_tex_2(B_104, A_105) | ~v2_tex_2(B_104, A_105) | ~v1_tops_1(B_104, A_105) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.45/1.79  tff(c_611, plain, (![B_104]: (v3_tex_2(B_104, '#skF_2') | ~v2_tex_2(B_104, '#skF_2') | ~v1_tops_1(B_104, '#skF_2') | ~m1_subset_1(B_104, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_605])).
% 4.45/1.79  tff(c_622, plain, (![B_104]: (v3_tex_2(B_104, '#skF_2') | ~v2_tex_2(B_104, '#skF_2') | ~v1_tops_1(B_104, '#skF_2') | ~m1_subset_1(B_104, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_611])).
% 4.45/1.79  tff(c_626, plain, (![B_106]: (v3_tex_2(B_106, '#skF_2') | ~v2_tex_2(B_106, '#skF_2') | ~v1_tops_1(B_106, '#skF_2') | ~m1_subset_1(B_106, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_622])).
% 4.45/1.79  tff(c_637, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_626])).
% 4.45/1.79  tff(c_642, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_310, c_637])).
% 4.45/1.79  tff(c_644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_642])).
% 4.45/1.79  tff(c_646, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 4.45/1.79  tff(c_707, plain, (![B_118, A_119]: (v2_tex_2(B_118, A_119) | ~v3_tex_2(B_118, A_119) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.45/1.79  tff(c_732, plain, (![A_122]: (v2_tex_2(u1_struct_0(A_122), A_122) | ~v3_tex_2(u1_struct_0(A_122), A_122) | ~l1_pre_topc(A_122))), inference(resolution, [status(thm)], [c_62, c_707])).
% 4.45/1.79  tff(c_735, plain, (v2_tex_2(u1_struct_0('#skF_2'), '#skF_2') | ~v3_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_657, c_732])).
% 4.45/1.79  tff(c_737, plain, (v2_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~v3_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_657, c_735])).
% 4.45/1.79  tff(c_738, plain, (~v3_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_737])).
% 4.45/1.79  tff(c_756, plain, (![B_124, A_125]: (v1_tops_1(B_124, A_125) | k2_pre_topc(A_125, B_124)!=u1_struct_0(A_125) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.45/1.80  tff(c_763, plain, (![B_124]: (v1_tops_1(B_124, '#skF_2') | k2_pre_topc('#skF_2', B_124)!=u1_struct_0('#skF_2') | ~m1_subset_1(B_124, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_657, c_756])).
% 4.45/1.80  tff(c_795, plain, (![B_129]: (v1_tops_1(B_129, '#skF_2') | k2_pre_topc('#skF_2', B_129)!=k2_struct_0('#skF_2') | ~m1_subset_1(B_129, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_657, c_763])).
% 4.45/1.80  tff(c_809, plain, (v1_tops_1(k2_struct_0('#skF_2'), '#skF_2') | k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_795])).
% 4.45/1.80  tff(c_811, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_809])).
% 4.45/1.80  tff(c_814, plain, (~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16, c_811])).
% 4.45/1.80  tff(c_818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_814])).
% 4.45/1.80  tff(c_819, plain, (v1_tops_1(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_809])).
% 4.45/1.80  tff(c_936, plain, (![B_141, A_142]: (v2_tex_2(B_141, A_142) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142) | ~v1_tdlat_3(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.45/1.80  tff(c_943, plain, (![B_141]: (v2_tex_2(B_141, '#skF_2') | ~m1_subset_1(B_141, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_657, c_936])).
% 4.45/1.80  tff(c_950, plain, (![B_141]: (v2_tex_2(B_141, '#skF_2') | ~m1_subset_1(B_141, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_943])).
% 4.45/1.80  tff(c_953, plain, (![B_143]: (v2_tex_2(B_143, '#skF_2') | ~m1_subset_1(B_143, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_950])).
% 4.45/1.80  tff(c_968, plain, (v2_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_62, c_953])).
% 4.45/1.80  tff(c_1145, plain, (![B_165, A_166]: (v3_tex_2(B_165, A_166) | ~v2_tex_2(B_165, A_166) | ~v1_tops_1(B_165, A_166) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.45/1.80  tff(c_1152, plain, (![B_165]: (v3_tex_2(B_165, '#skF_2') | ~v2_tex_2(B_165, '#skF_2') | ~v1_tops_1(B_165, '#skF_2') | ~m1_subset_1(B_165, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_657, c_1145])).
% 4.45/1.80  tff(c_1159, plain, (![B_165]: (v3_tex_2(B_165, '#skF_2') | ~v2_tex_2(B_165, '#skF_2') | ~v1_tops_1(B_165, '#skF_2') | ~m1_subset_1(B_165, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_1152])).
% 4.45/1.80  tff(c_1162, plain, (![B_167]: (v3_tex_2(B_167, '#skF_2') | ~v2_tex_2(B_167, '#skF_2') | ~v1_tops_1(B_167, '#skF_2') | ~m1_subset_1(B_167, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_1159])).
% 4.45/1.80  tff(c_1173, plain, (v3_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~v2_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~v1_tops_1(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_62, c_1162])).
% 4.45/1.80  tff(c_1180, plain, (v3_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_819, c_968, c_1173])).
% 4.45/1.80  tff(c_1182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_738, c_1180])).
% 4.45/1.80  tff(c_1183, plain, (v2_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_737])).
% 4.45/1.80  tff(c_667, plain, (![A_112, B_113]: (r1_tarski(A_112, B_113) | ~m1_subset_1(A_112, k1_zfmisc_1(B_113)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.45/1.80  tff(c_678, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_661, c_667])).
% 4.45/1.80  tff(c_2385, plain, (![C_277, B_278, A_279]: (C_277=B_278 | ~r1_tarski(B_278, C_277) | ~v2_tex_2(C_277, A_279) | ~m1_subset_1(C_277, k1_zfmisc_1(u1_struct_0(A_279))) | ~v3_tex_2(B_278, A_279) | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0(A_279))) | ~l1_pre_topc(A_279))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.45/1.80  tff(c_2399, plain, (![A_279]: (k2_struct_0('#skF_2')='#skF_3' | ~v2_tex_2(k2_struct_0('#skF_2'), A_279) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_279))) | ~v3_tex_2('#skF_3', A_279) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_279))) | ~l1_pre_topc(A_279))), inference(resolution, [status(thm)], [c_678, c_2385])).
% 4.45/1.80  tff(c_2495, plain, (![A_287]: (~v2_tex_2(k2_struct_0('#skF_2'), A_287) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_287))) | ~v3_tex_2('#skF_3', A_287) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_287))) | ~l1_pre_topc(A_287))), inference(splitLeft, [status(thm)], [c_2399])).
% 4.45/1.80  tff(c_2501, plain, (~v2_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_657, c_2495])).
% 4.45/1.80  tff(c_2505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_661, c_657, c_646, c_62, c_1183, c_2501])).
% 4.45/1.80  tff(c_2506, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_2399])).
% 4.45/1.80  tff(c_645, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_54])).
% 4.45/1.80  tff(c_660, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_657, c_645])).
% 4.45/1.80  tff(c_2532, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2506, c_660])).
% 4.45/1.80  tff(c_2540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_2532])).
% 4.45/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.80  
% 4.45/1.80  Inference rules
% 4.45/1.80  ----------------------
% 4.45/1.80  #Ref     : 0
% 4.45/1.80  #Sup     : 454
% 4.45/1.80  #Fact    : 0
% 4.45/1.80  #Define  : 0
% 4.45/1.80  #Split   : 9
% 4.45/1.80  #Chain   : 0
% 4.45/1.80  #Close   : 0
% 4.45/1.80  
% 4.45/1.80  Ordering : KBO
% 4.45/1.80  
% 4.45/1.80  Simplification rules
% 4.45/1.80  ----------------------
% 4.45/1.80  #Subsume      : 92
% 4.45/1.80  #Demod        : 528
% 4.45/1.80  #Tautology    : 143
% 4.45/1.80  #SimpNegUnit  : 44
% 4.45/1.80  #BackRed      : 63
% 4.45/1.80  
% 4.45/1.80  #Partial instantiations: 0
% 4.45/1.80  #Strategies tried      : 1
% 4.45/1.80  
% 4.45/1.80  Timing (in seconds)
% 4.45/1.80  ----------------------
% 4.45/1.80  Preprocessing        : 0.31
% 4.45/1.80  Parsing              : 0.16
% 4.45/1.80  CNF conversion       : 0.02
% 4.45/1.80  Main loop            : 0.70
% 4.45/1.80  Inferencing          : 0.26
% 4.45/1.80  Reduction            : 0.22
% 4.45/1.80  Demodulation         : 0.15
% 4.45/1.80  BG Simplification    : 0.03
% 4.45/1.80  Subsumption          : 0.14
% 4.45/1.80  Abstraction          : 0.04
% 4.45/1.80  MUC search           : 0.00
% 4.45/1.80  Cooper               : 0.00
% 4.45/1.80  Total                : 1.05
% 4.45/1.80  Index Insertion      : 0.00
% 4.45/1.80  Index Deletion       : 0.00
% 4.45/1.80  Index Matching       : 0.00
% 4.45/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
