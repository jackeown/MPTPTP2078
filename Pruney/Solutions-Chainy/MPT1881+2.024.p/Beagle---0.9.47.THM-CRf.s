%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:09 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 407 expanded)
%              Number of leaves         :   38 ( 151 expanded)
%              Depth                    :   10
%              Number of atoms          :  284 (1245 expanded)
%              Number of equality atoms :   35 ( 127 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_161,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_143,axiom,(
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

tff(f_127,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_6] : ~ v1_subset_1(k2_subset_1(A_6),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_61,plain,(
    ! [A_6] : ~ v1_subset_1(A_6,A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1847,plain,(
    ! [A_191,B_192] :
      ( k2_pre_topc(A_191,B_192) = B_192
      | ~ v4_pre_topc(B_192,A_191)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ l1_pre_topc(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1857,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1847])).

tff(c_1862,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1857])).

tff(c_1863,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1862])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_48,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1722,plain,(
    ! [A_174,B_175] :
      ( k4_xboole_0(A_174,B_175) = k3_subset_1(A_174,B_175)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(A_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1730,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1722])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1734,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1730,c_2])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1864,plain,(
    ! [B_193,A_194] :
      ( v3_pre_topc(B_193,A_194)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ v1_tdlat_3(A_194)
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1934,plain,(
    ! [A_197,A_198] :
      ( v3_pre_topc(A_197,A_198)
      | ~ v1_tdlat_3(A_198)
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198)
      | ~ r1_tarski(A_197,u1_struct_0(A_198)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1864])).

tff(c_1962,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1734,c_1934])).

tff(c_1983,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_48,c_1962])).

tff(c_2348,plain,(
    ! [B_214,A_215] :
      ( v4_pre_topc(B_214,A_215)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_215),B_214),A_215)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2363,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1983,c_2348])).

tff(c_2376,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2363])).

tff(c_2378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1863,c_2376])).

tff(c_2379,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1862])).

tff(c_2525,plain,(
    ! [B_222,A_223] :
      ( v1_tops_1(B_222,A_223)
      | k2_pre_topc(A_223,B_222) != u1_struct_0(A_223)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2535,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_2525])).

tff(c_2540,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | u1_struct_0('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2379,c_2535])).

tff(c_2541,plain,(
    u1_struct_0('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2540])).

tff(c_2722,plain,(
    ! [A_230,B_231] :
      ( k2_pre_topc(A_230,B_231) = u1_struct_0(A_230)
      | ~ v1_tops_1(B_231,A_230)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2732,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = u1_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_2722])).

tff(c_2737,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2379,c_2732])).

tff(c_2738,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_2541,c_2737])).

tff(c_2449,plain,(
    ! [B_218,A_219] :
      ( v3_pre_topc(B_218,A_219)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ v1_tdlat_3(A_219)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2459,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_2449])).

tff(c_2464,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_48,c_2459])).

tff(c_60,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_74,plain,(
    ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_80,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_54])).

tff(c_86,plain,(
    ! [B_44,A_45] :
      ( v1_subset_1(B_44,A_45)
      | B_44 = A_45
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_92,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_86])).

tff(c_96,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_92])).

tff(c_99,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_44])).

tff(c_256,plain,(
    ! [A_61,B_62] :
      ( k2_pre_topc(A_61,B_62) = B_62
      | ~ v4_pre_topc(B_62,A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_262,plain,(
    ! [B_62] :
      ( k2_pre_topc('#skF_2',B_62) = B_62
      | ~ v4_pre_topc(B_62,'#skF_2')
      | ~ m1_subset_1(B_62,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_256])).

tff(c_271,plain,(
    ! [B_63] :
      ( k2_pre_topc('#skF_2',B_63) = B_63
      | ~ v4_pre_topc(B_63,'#skF_2')
      | ~ m1_subset_1(B_63,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_262])).

tff(c_279,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_99,c_271])).

tff(c_281,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_116,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = k3_subset_1(A_46,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_123,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_subset_1('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_99,c_116])).

tff(c_324,plain,(
    ! [B_67,A_68] :
      ( v3_pre_topc(B_67,A_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ v1_tdlat_3(A_68)
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_391,plain,(
    ! [A_73,A_74] :
      ( v3_pre_topc(A_73,A_74)
      | ~ v1_tdlat_3(A_74)
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | ~ r1_tarski(A_73,u1_struct_0(A_74)) ) ),
    inference(resolution,[status(thm)],[c_12,c_324])).

tff(c_421,plain,(
    ! [A_75,B_76] :
      ( v3_pre_topc(k4_xboole_0(u1_struct_0(A_75),B_76),A_75)
      | ~ v1_tdlat_3(A_75)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_2,c_391])).

tff(c_428,plain,(
    ! [B_76] :
      ( v3_pre_topc(k4_xboole_0('#skF_3',B_76),'#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_421])).

tff(c_431,plain,(
    ! [B_77] : v3_pre_topc(k4_xboole_0('#skF_3',B_77),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_48,c_428])).

tff(c_441,plain,(
    v3_pre_topc(k3_subset_1('#skF_3','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_431])).

tff(c_574,plain,(
    ! [B_91,A_92] :
      ( v4_pre_topc(B_91,A_92)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_92),B_91),A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_581,plain,(
    ! [B_91] :
      ( v4_pre_topc(B_91,'#skF_2')
      | ~ v3_pre_topc(k3_subset_1('#skF_3',B_91),'#skF_2')
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_574])).

tff(c_587,plain,(
    ! [B_93] :
      ( v4_pre_topc(B_93,'#skF_2')
      | ~ v3_pre_topc(k3_subset_1('#skF_3',B_93),'#skF_2')
      | ~ m1_subset_1(B_93,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_96,c_581])).

tff(c_611,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_441,c_587])).

tff(c_624,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_611])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_624])).

tff(c_627,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_852,plain,(
    ! [B_114,A_115] :
      ( v1_tops_1(B_114,A_115)
      | k2_pre_topc(A_115,B_114) != u1_struct_0(A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_858,plain,(
    ! [B_114] :
      ( v1_tops_1(B_114,'#skF_2')
      | k2_pre_topc('#skF_2',B_114) != u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_114,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_852])).

tff(c_867,plain,(
    ! [B_116] :
      ( v1_tops_1(B_116,'#skF_2')
      | k2_pre_topc('#skF_2',B_116) != '#skF_3'
      | ~ m1_subset_1(B_116,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_96,c_858])).

tff(c_870,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_99,c_867])).

tff(c_877,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_870])).

tff(c_1137,plain,(
    ! [B_131,A_132] :
      ( v2_tex_2(B_131,A_132)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132)
      | ~ v1_tdlat_3(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1143,plain,(
    ! [B_131] :
      ( v2_tex_2(B_131,'#skF_2')
      | ~ m1_subset_1(B_131,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1137])).

tff(c_1150,plain,(
    ! [B_131] :
      ( v2_tex_2(B_131,'#skF_2')
      | ~ m1_subset_1(B_131,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_1143])).

tff(c_1153,plain,(
    ! [B_133] :
      ( v2_tex_2(B_133,'#skF_2')
      | ~ m1_subset_1(B_133,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1150])).

tff(c_1161,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_99,c_1153])).

tff(c_1647,plain,(
    ! [B_162,A_163] :
      ( v3_tex_2(B_162,A_163)
      | ~ v2_tex_2(B_162,A_163)
      | ~ v1_tops_1(B_162,A_163)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1653,plain,(
    ! [B_162] :
      ( v3_tex_2(B_162,'#skF_2')
      | ~ v2_tex_2(B_162,'#skF_2')
      | ~ v1_tops_1(B_162,'#skF_2')
      | ~ m1_subset_1(B_162,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1647])).

tff(c_1660,plain,(
    ! [B_162] :
      ( v3_tex_2(B_162,'#skF_2')
      | ~ v2_tex_2(B_162,'#skF_2')
      | ~ v1_tops_1(B_162,'#skF_2')
      | ~ m1_subset_1(B_162,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_1653])).

tff(c_1678,plain,(
    ! [B_165] :
      ( v3_tex_2(B_165,'#skF_2')
      | ~ v2_tex_2(B_165,'#skF_2')
      | ~ v1_tops_1(B_165,'#skF_2')
      | ~ m1_subset_1(B_165,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1660])).

tff(c_1681,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_99,c_1678])).

tff(c_1688,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_1161,c_1681])).

tff(c_1690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1688])).

tff(c_1691,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_3296,plain,(
    ! [B_256,A_257] :
      ( v1_tops_1(B_256,A_257)
      | ~ v3_tex_2(B_256,A_257)
      | ~ v3_pre_topc(B_256,A_257)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257)
      | v2_struct_0(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3309,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_3296])).

tff(c_3318,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_2464,c_1691,c_3309])).

tff(c_3320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2738,c_3318])).

tff(c_3322,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2540])).

tff(c_1692,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_3331,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3322,c_1692])).

tff(c_3334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_3331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:15:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.78/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.78/1.86  
% 4.78/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.78/1.86  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 4.78/1.86  
% 4.78/1.86  %Foreground sorts:
% 4.78/1.86  
% 4.78/1.86  
% 4.78/1.86  %Background operators:
% 4.78/1.86  
% 4.78/1.86  
% 4.78/1.86  %Foreground operators:
% 4.78/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.78/1.86  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.78/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.78/1.86  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.78/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.78/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.78/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.78/1.86  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.78/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.78/1.86  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.78/1.86  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.78/1.86  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.78/1.86  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.78/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.78/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.78/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.78/1.86  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.78/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.78/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.78/1.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.78/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.78/1.86  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.78/1.86  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.78/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.78/1.86  
% 4.78/1.88  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.78/1.88  tff(f_36, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 4.78/1.88  tff(f_161, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 4.78/1.88  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.78/1.88  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.78/1.88  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.78/1.88  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.78/1.88  tff(f_97, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 4.78/1.88  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 4.78/1.88  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 4.78/1.88  tff(f_86, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 4.78/1.88  tff(f_111, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 4.78/1.88  tff(f_143, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 4.78/1.88  tff(f_127, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 4.78/1.88  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.78/1.88  tff(c_8, plain, (![A_6]: (~v1_subset_1(k2_subset_1(A_6), A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.78/1.88  tff(c_61, plain, (![A_6]: (~v1_subset_1(A_6, A_6))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 4.78/1.88  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.78/1.88  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.78/1.88  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.78/1.88  tff(c_1847, plain, (![A_191, B_192]: (k2_pre_topc(A_191, B_192)=B_192 | ~v4_pre_topc(B_192, A_191) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_191))) | ~l1_pre_topc(A_191))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.78/1.88  tff(c_1857, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_1847])).
% 4.78/1.88  tff(c_1862, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1857])).
% 4.78/1.88  tff(c_1863, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1862])).
% 4.78/1.88  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.78/1.88  tff(c_48, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.78/1.88  tff(c_1722, plain, (![A_174, B_175]: (k4_xboole_0(A_174, B_175)=k3_subset_1(A_174, B_175) | ~m1_subset_1(B_175, k1_zfmisc_1(A_174)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.78/1.88  tff(c_1730, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_44, c_1722])).
% 4.78/1.88  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.78/1.88  tff(c_1734, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1730, c_2])).
% 4.78/1.88  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.78/1.88  tff(c_1864, plain, (![B_193, A_194]: (v3_pre_topc(B_193, A_194) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_194))) | ~v1_tdlat_3(A_194) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.78/1.88  tff(c_1934, plain, (![A_197, A_198]: (v3_pre_topc(A_197, A_198) | ~v1_tdlat_3(A_198) | ~l1_pre_topc(A_198) | ~v2_pre_topc(A_198) | ~r1_tarski(A_197, u1_struct_0(A_198)))), inference(resolution, [status(thm)], [c_12, c_1864])).
% 4.78/1.88  tff(c_1962, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1734, c_1934])).
% 4.78/1.88  tff(c_1983, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_48, c_1962])).
% 4.78/1.88  tff(c_2348, plain, (![B_214, A_215]: (v4_pre_topc(B_214, A_215) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_215), B_214), A_215) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.78/1.88  tff(c_2363, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1983, c_2348])).
% 4.78/1.88  tff(c_2376, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2363])).
% 4.78/1.88  tff(c_2378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1863, c_2376])).
% 4.78/1.88  tff(c_2379, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1862])).
% 4.78/1.88  tff(c_2525, plain, (![B_222, A_223]: (v1_tops_1(B_222, A_223) | k2_pre_topc(A_223, B_222)!=u1_struct_0(A_223) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.78/1.88  tff(c_2535, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_2525])).
% 4.78/1.88  tff(c_2540, plain, (v1_tops_1('#skF_3', '#skF_2') | u1_struct_0('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2379, c_2535])).
% 4.78/1.88  tff(c_2541, plain, (u1_struct_0('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_2540])).
% 4.78/1.88  tff(c_2722, plain, (![A_230, B_231]: (k2_pre_topc(A_230, B_231)=u1_struct_0(A_230) | ~v1_tops_1(B_231, A_230) | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.78/1.88  tff(c_2732, plain, (k2_pre_topc('#skF_2', '#skF_3')=u1_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_2722])).
% 4.78/1.88  tff(c_2737, plain, (u1_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2379, c_2732])).
% 4.78/1.88  tff(c_2738, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_2541, c_2737])).
% 4.78/1.88  tff(c_2449, plain, (![B_218, A_219]: (v3_pre_topc(B_218, A_219) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0(A_219))) | ~v1_tdlat_3(A_219) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.78/1.88  tff(c_2459, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_2449])).
% 4.78/1.88  tff(c_2464, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_48, c_2459])).
% 4.78/1.88  tff(c_60, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.78/1.88  tff(c_74, plain, (~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_60])).
% 4.78/1.88  tff(c_54, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.78/1.88  tff(c_80, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_74, c_54])).
% 4.78/1.88  tff(c_86, plain, (![B_44, A_45]: (v1_subset_1(B_44, A_45) | B_44=A_45 | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.78/1.88  tff(c_92, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_44, c_86])).
% 4.78/1.88  tff(c_96, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_74, c_92])).
% 4.78/1.88  tff(c_99, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_44])).
% 4.78/1.88  tff(c_256, plain, (![A_61, B_62]: (k2_pre_topc(A_61, B_62)=B_62 | ~v4_pre_topc(B_62, A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.78/1.88  tff(c_262, plain, (![B_62]: (k2_pre_topc('#skF_2', B_62)=B_62 | ~v4_pre_topc(B_62, '#skF_2') | ~m1_subset_1(B_62, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_256])).
% 4.78/1.88  tff(c_271, plain, (![B_63]: (k2_pre_topc('#skF_2', B_63)=B_63 | ~v4_pre_topc(B_63, '#skF_2') | ~m1_subset_1(B_63, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_262])).
% 4.78/1.88  tff(c_279, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_99, c_271])).
% 4.78/1.88  tff(c_281, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_279])).
% 4.78/1.88  tff(c_116, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=k3_subset_1(A_46, B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.78/1.88  tff(c_123, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_subset_1('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_99, c_116])).
% 4.78/1.89  tff(c_324, plain, (![B_67, A_68]: (v3_pre_topc(B_67, A_68) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_68))) | ~v1_tdlat_3(A_68) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.78/1.89  tff(c_391, plain, (![A_73, A_74]: (v3_pre_topc(A_73, A_74) | ~v1_tdlat_3(A_74) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | ~r1_tarski(A_73, u1_struct_0(A_74)))), inference(resolution, [status(thm)], [c_12, c_324])).
% 4.78/1.89  tff(c_421, plain, (![A_75, B_76]: (v3_pre_topc(k4_xboole_0(u1_struct_0(A_75), B_76), A_75) | ~v1_tdlat_3(A_75) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(resolution, [status(thm)], [c_2, c_391])).
% 4.78/1.89  tff(c_428, plain, (![B_76]: (v3_pre_topc(k4_xboole_0('#skF_3', B_76), '#skF_2') | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_421])).
% 4.78/1.89  tff(c_431, plain, (![B_77]: (v3_pre_topc(k4_xboole_0('#skF_3', B_77), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_48, c_428])).
% 4.78/1.89  tff(c_441, plain, (v3_pre_topc(k3_subset_1('#skF_3', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_123, c_431])).
% 4.78/1.89  tff(c_574, plain, (![B_91, A_92]: (v4_pre_topc(B_91, A_92) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_92), B_91), A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.78/1.89  tff(c_581, plain, (![B_91]: (v4_pre_topc(B_91, '#skF_2') | ~v3_pre_topc(k3_subset_1('#skF_3', B_91), '#skF_2') | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_574])).
% 4.78/1.89  tff(c_587, plain, (![B_93]: (v4_pre_topc(B_93, '#skF_2') | ~v3_pre_topc(k3_subset_1('#skF_3', B_93), '#skF_2') | ~m1_subset_1(B_93, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_96, c_581])).
% 4.78/1.89  tff(c_611, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_441, c_587])).
% 4.78/1.89  tff(c_624, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_611])).
% 4.78/1.89  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_281, c_624])).
% 4.78/1.89  tff(c_627, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_279])).
% 4.78/1.89  tff(c_852, plain, (![B_114, A_115]: (v1_tops_1(B_114, A_115) | k2_pre_topc(A_115, B_114)!=u1_struct_0(A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.78/1.89  tff(c_858, plain, (![B_114]: (v1_tops_1(B_114, '#skF_2') | k2_pre_topc('#skF_2', B_114)!=u1_struct_0('#skF_2') | ~m1_subset_1(B_114, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_852])).
% 4.78/1.89  tff(c_867, plain, (![B_116]: (v1_tops_1(B_116, '#skF_2') | k2_pre_topc('#skF_2', B_116)!='#skF_3' | ~m1_subset_1(B_116, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_96, c_858])).
% 4.78/1.89  tff(c_870, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_99, c_867])).
% 4.78/1.89  tff(c_877, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_627, c_870])).
% 4.78/1.89  tff(c_1137, plain, (![B_131, A_132]: (v2_tex_2(B_131, A_132) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132) | ~v1_tdlat_3(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.78/1.89  tff(c_1143, plain, (![B_131]: (v2_tex_2(B_131, '#skF_2') | ~m1_subset_1(B_131, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_1137])).
% 4.78/1.89  tff(c_1150, plain, (![B_131]: (v2_tex_2(B_131, '#skF_2') | ~m1_subset_1(B_131, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_1143])).
% 4.78/1.89  tff(c_1153, plain, (![B_133]: (v2_tex_2(B_133, '#skF_2') | ~m1_subset_1(B_133, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_1150])).
% 4.78/1.89  tff(c_1161, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_99, c_1153])).
% 4.78/1.89  tff(c_1647, plain, (![B_162, A_163]: (v3_tex_2(B_162, A_163) | ~v2_tex_2(B_162, A_163) | ~v1_tops_1(B_162, A_163) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.78/1.89  tff(c_1653, plain, (![B_162]: (v3_tex_2(B_162, '#skF_2') | ~v2_tex_2(B_162, '#skF_2') | ~v1_tops_1(B_162, '#skF_2') | ~m1_subset_1(B_162, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_1647])).
% 4.78/1.89  tff(c_1660, plain, (![B_162]: (v3_tex_2(B_162, '#skF_2') | ~v2_tex_2(B_162, '#skF_2') | ~v1_tops_1(B_162, '#skF_2') | ~m1_subset_1(B_162, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_1653])).
% 4.78/1.89  tff(c_1678, plain, (![B_165]: (v3_tex_2(B_165, '#skF_2') | ~v2_tex_2(B_165, '#skF_2') | ~v1_tops_1(B_165, '#skF_2') | ~m1_subset_1(B_165, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_1660])).
% 4.78/1.89  tff(c_1681, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_99, c_1678])).
% 4.78/1.89  tff(c_1688, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_877, c_1161, c_1681])).
% 4.78/1.89  tff(c_1690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1688])).
% 4.78/1.89  tff(c_1691, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 4.78/1.89  tff(c_3296, plain, (![B_256, A_257]: (v1_tops_1(B_256, A_257) | ~v3_tex_2(B_256, A_257) | ~v3_pre_topc(B_256, A_257) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_257))) | ~l1_pre_topc(A_257) | ~v2_pre_topc(A_257) | v2_struct_0(A_257))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.78/1.89  tff(c_3309, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_3296])).
% 4.78/1.89  tff(c_3318, plain, (v1_tops_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_2464, c_1691, c_3309])).
% 4.78/1.89  tff(c_3320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_2738, c_3318])).
% 4.78/1.89  tff(c_3322, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_2540])).
% 4.78/1.89  tff(c_1692, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_60])).
% 4.78/1.89  tff(c_3331, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3322, c_1692])).
% 4.78/1.89  tff(c_3334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_3331])).
% 4.78/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.78/1.89  
% 4.78/1.89  Inference rules
% 4.78/1.89  ----------------------
% 4.78/1.89  #Ref     : 0
% 4.78/1.89  #Sup     : 698
% 4.78/1.89  #Fact    : 0
% 4.78/1.89  #Define  : 0
% 4.78/1.89  #Split   : 9
% 4.78/1.89  #Chain   : 0
% 4.78/1.89  #Close   : 0
% 4.78/1.89  
% 4.78/1.89  Ordering : KBO
% 4.78/1.89  
% 4.78/1.89  Simplification rules
% 4.78/1.89  ----------------------
% 4.78/1.89  #Subsume      : 24
% 4.78/1.89  #Demod        : 505
% 4.78/1.89  #Tautology    : 209
% 4.78/1.89  #SimpNegUnit  : 35
% 4.78/1.89  #BackRed      : 14
% 4.78/1.89  
% 4.78/1.89  #Partial instantiations: 0
% 4.78/1.89  #Strategies tried      : 1
% 4.78/1.89  
% 4.78/1.89  Timing (in seconds)
% 4.78/1.89  ----------------------
% 4.78/1.89  Preprocessing        : 0.34
% 4.78/1.89  Parsing              : 0.18
% 4.78/1.89  CNF conversion       : 0.02
% 4.78/1.89  Main loop            : 0.77
% 4.78/1.89  Inferencing          : 0.28
% 4.78/1.89  Reduction            : 0.27
% 4.78/1.89  Demodulation         : 0.20
% 4.78/1.89  BG Simplification    : 0.04
% 4.78/1.89  Subsumption          : 0.12
% 4.78/1.89  Abstraction          : 0.05
% 4.78/1.89  MUC search           : 0.00
% 4.78/1.89  Cooper               : 0.00
% 4.78/1.89  Total                : 1.16
% 4.78/1.89  Index Insertion      : 0.00
% 4.78/1.89  Index Deletion       : 0.00
% 4.78/1.89  Index Matching       : 0.00
% 4.78/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
