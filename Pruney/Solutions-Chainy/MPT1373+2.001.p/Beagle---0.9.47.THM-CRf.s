%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:01 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 408 expanded)
%              Number of leaves         :   30 ( 155 expanded)
%              Depth                    :   19
%              Number of atoms          :  221 (1285 expanded)
%              Number of equality atoms :   19 ( 124 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_compts_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( C = D
                     => ( v2_compts_1(C,A)
                      <=> v2_compts_1(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_compts_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(C,k2_struct_0(B))
               => ( v2_compts_1(C,A)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( D = C
                       => v2_compts_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).

tff(c_56,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_54,plain,(
    m1_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_74,plain,(
    ! [B_86,A_87] :
      ( l1_pre_topc(B_86)
      | ~ m1_pre_topc(B_86,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_77,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_74])).

tff(c_80,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_77])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_94,plain,(
    ! [A_90,B_91] :
      ( m1_pre_topc(k1_pre_topc(A_90,B_91),A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_98,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),'#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_94])).

tff(c_104,plain,(
    m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_98])).

tff(c_38,plain,(
    ! [B_52,A_50] :
      ( l1_pre_topc(B_52)
      | ~ m1_pre_topc(B_52,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_114,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_6','#skF_8'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_38])).

tff(c_117,plain,(
    l1_pre_topc(k1_pre_topc('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_114])).

tff(c_81,plain,(
    ! [A_88,B_89] :
      ( v1_pre_topc(k1_pre_topc(A_88,B_89))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_87,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_6','#skF_8'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_81])).

tff(c_93,plain,(
    v1_pre_topc(k1_pre_topc('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_87])).

tff(c_135,plain,(
    ! [A_102,B_103] :
      ( k2_struct_0(k1_pre_topc(A_102,B_103)) = B_103
      | ~ m1_pre_topc(k1_pre_topc(A_102,B_103),A_102)
      | ~ v1_pre_topc(k1_pre_topc(A_102,B_103))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_137,plain,
    ( k2_struct_0(k1_pre_topc('#skF_6','#skF_8')) = '#skF_8'
    | ~ v1_pre_topc(k1_pre_topc('#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_135])).

tff(c_142,plain,(
    k2_struct_0(k1_pre_topc('#skF_6','#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_50,c_93,c_137])).

tff(c_24,plain,(
    ! [B_30,A_8] :
      ( r1_tarski(k2_struct_0(B_30),k2_struct_0(A_8))
      | ~ m1_pre_topc(B_30,A_8)
      | ~ l1_pre_topc(B_30)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_160,plain,(
    ! [A_8] :
      ( r1_tarski('#skF_8',k2_struct_0(A_8))
      | ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),A_8)
      | ~ l1_pre_topc(k1_pre_topc('#skF_6','#skF_8'))
      | ~ l1_pre_topc(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_24])).

tff(c_177,plain,(
    ! [A_8] :
      ( r1_tarski('#skF_8',k2_struct_0(A_8))
      | ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_160])).

tff(c_48,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_58,plain,
    ( ~ v2_compts_1('#skF_8','#skF_6')
    | ~ v2_compts_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_65,plain,
    ( ~ v2_compts_1('#skF_8','#skF_6')
    | ~ v2_compts_1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_58])).

tff(c_72,plain,(
    ~ v2_compts_1('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_66,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52])).

tff(c_64,plain,
    ( v2_compts_1('#skF_7','#skF_5')
    | v2_compts_1('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_67,plain,
    ( v2_compts_1('#skF_8','#skF_5')
    | v2_compts_1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_64])).

tff(c_73,plain,(
    v2_compts_1('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_67])).

tff(c_270,plain,(
    ! [A_114] :
      ( r1_tarski('#skF_8',k2_struct_0(A_114))
      | ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_160])).

tff(c_44,plain,(
    ! [A_53,B_65,C_71] :
      ( '#skF_4'(A_53,B_65,C_71) = C_71
      | v2_compts_1(C_71,A_53)
      | ~ r1_tarski(C_71,k2_struct_0(B_65))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_pre_topc(B_65,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_606,plain,(
    ! [A_167,A_168] :
      ( '#skF_4'(A_167,A_168,'#skF_8') = '#skF_8'
      | v2_compts_1('#skF_8',A_167)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ m1_pre_topc(A_168,A_167)
      | ~ l1_pre_topc(A_167)
      | ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),A_168)
      | ~ l1_pre_topc(A_168) ) ),
    inference(resolution,[status(thm)],[c_270,c_44])).

tff(c_608,plain,(
    ! [A_168] :
      ( '#skF_4'('#skF_5',A_168,'#skF_8') = '#skF_8'
      | v2_compts_1('#skF_8','#skF_5')
      | ~ m1_pre_topc(A_168,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),A_168)
      | ~ l1_pre_topc(A_168) ) ),
    inference(resolution,[status(thm)],[c_66,c_606])).

tff(c_613,plain,(
    ! [A_168] :
      ( '#skF_4'('#skF_5',A_168,'#skF_8') = '#skF_8'
      | v2_compts_1('#skF_8','#skF_5')
      | ~ m1_pre_topc(A_168,'#skF_5')
      | ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),A_168)
      | ~ l1_pre_topc(A_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_608])).

tff(c_618,plain,(
    ! [A_169] :
      ( '#skF_4'('#skF_5',A_169,'#skF_8') = '#skF_8'
      | ~ m1_pre_topc(A_169,'#skF_5')
      | ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),A_169)
      | ~ l1_pre_topc(A_169) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_613])).

tff(c_621,plain,
    ( '#skF_4'('#skF_5','#skF_6','#skF_8') = '#skF_8'
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_618])).

tff(c_624,plain,(
    '#skF_4'('#skF_5','#skF_6','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_54,c_621])).

tff(c_42,plain,(
    ! [A_53,B_65,C_71] :
      ( ~ v2_compts_1('#skF_4'(A_53,B_65,C_71),B_65)
      | v2_compts_1(C_71,A_53)
      | ~ r1_tarski(C_71,k2_struct_0(B_65))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_pre_topc(B_65,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_630,plain,
    ( ~ v2_compts_1('#skF_8','#skF_6')
    | v2_compts_1('#skF_8','#skF_5')
    | ~ r1_tarski('#skF_8',k2_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_624,c_42])).

tff(c_637,plain,
    ( v2_compts_1('#skF_8','#skF_5')
    | ~ r1_tarski('#skF_8',k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_66,c_73,c_630])).

tff(c_638,plain,(
    ~ r1_tarski('#skF_8',k2_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_637])).

tff(c_645,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),'#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_177,c_638])).

tff(c_652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_104,c_645])).

tff(c_654,plain,(
    v2_compts_1('#skF_8','#skF_5') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_657,plain,(
    ! [B_170,A_171] :
      ( l1_pre_topc(B_170)
      | ~ m1_pre_topc(B_170,A_171)
      | ~ l1_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_660,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_657])).

tff(c_663,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_660])).

tff(c_678,plain,(
    ! [A_176,B_177] :
      ( m1_pre_topc(k1_pre_topc(A_176,B_177),A_176)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_682,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),'#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_678])).

tff(c_688,plain,(
    m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_682])).

tff(c_697,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_6','#skF_8'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_688,c_38])).

tff(c_700,plain,(
    l1_pre_topc(k1_pre_topc('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_697])).

tff(c_664,plain,(
    ! [A_172,B_173] :
      ( v1_pre_topc(k1_pre_topc(A_172,B_173))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_674,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_6','#skF_8'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_664])).

tff(c_676,plain,(
    v1_pre_topc(k1_pre_topc('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_674])).

tff(c_718,plain,(
    ! [A_186,B_187] :
      ( k2_struct_0(k1_pre_topc(A_186,B_187)) = B_187
      | ~ m1_pre_topc(k1_pre_topc(A_186,B_187),A_186)
      | ~ v1_pre_topc(k1_pre_topc(A_186,B_187))
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ l1_pre_topc(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_720,plain,
    ( k2_struct_0(k1_pre_topc('#skF_6','#skF_8')) = '#skF_8'
    | ~ v1_pre_topc(k1_pre_topc('#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_688,c_718])).

tff(c_725,plain,(
    k2_struct_0(k1_pre_topc('#skF_6','#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_50,c_676,c_720])).

tff(c_743,plain,(
    ! [A_8] :
      ( r1_tarski('#skF_8',k2_struct_0(A_8))
      | ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),A_8)
      | ~ l1_pre_topc(k1_pre_topc('#skF_6','#skF_8'))
      | ~ l1_pre_topc(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_725,c_24])).

tff(c_760,plain,(
    ! [A_8] :
      ( r1_tarski('#skF_8',k2_struct_0(A_8))
      | ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_743])).

tff(c_653,plain,(
    ~ v2_compts_1('#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_1031,plain,(
    ! [D_231,B_232,A_233] :
      ( v2_compts_1(D_231,B_232)
      | ~ m1_subset_1(D_231,k1_zfmisc_1(u1_struct_0(B_232)))
      | ~ v2_compts_1(D_231,A_233)
      | ~ r1_tarski(D_231,k2_struct_0(B_232))
      | ~ m1_subset_1(D_231,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ m1_pre_topc(B_232,A_233)
      | ~ l1_pre_topc(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1041,plain,(
    ! [A_233] :
      ( v2_compts_1('#skF_8','#skF_6')
      | ~ v2_compts_1('#skF_8',A_233)
      | ~ r1_tarski('#skF_8',k2_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ m1_pre_topc('#skF_6',A_233)
      | ~ l1_pre_topc(A_233) ) ),
    inference(resolution,[status(thm)],[c_50,c_1031])).

tff(c_1049,plain,(
    ! [A_233] :
      ( ~ v2_compts_1('#skF_8',A_233)
      | ~ r1_tarski('#skF_8',k2_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ m1_pre_topc('#skF_6',A_233)
      | ~ l1_pre_topc(A_233) ) ),
    inference(negUnitSimplification,[status(thm)],[c_653,c_1041])).

tff(c_1050,plain,(
    ~ r1_tarski('#skF_8',k2_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1049])).

tff(c_1056,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),'#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_760,c_1050])).

tff(c_1063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_688,c_1056])).

tff(c_1069,plain,(
    ! [A_234] :
      ( ~ v2_compts_1('#skF_8',A_234)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ m1_pre_topc('#skF_6',A_234)
      | ~ l1_pre_topc(A_234) ) ),
    inference(splitRight,[status(thm)],[c_1049])).

tff(c_1072,plain,
    ( ~ v2_compts_1('#skF_8','#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1069])).

tff(c_1079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_654,c_1072])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.72  
% 3.82/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.72  %$ v2_compts_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 3.82/1.72  
% 3.82/1.72  %Foreground sorts:
% 3.82/1.72  
% 3.82/1.72  
% 3.82/1.72  %Background operators:
% 3.82/1.72  
% 3.82/1.72  
% 3.82/1.72  %Foreground operators:
% 3.82/1.72  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 3.82/1.72  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 3.82/1.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.82/1.72  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.82/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.82/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.82/1.72  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.82/1.72  tff('#skF_7', type, '#skF_7': $i).
% 3.82/1.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.82/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/1.72  tff('#skF_5', type, '#skF_5': $i).
% 3.82/1.72  tff('#skF_6', type, '#skF_6': $i).
% 3.82/1.72  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.82/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.82/1.72  tff('#skF_8', type, '#skF_8': $i).
% 3.82/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.82/1.72  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.82/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.82/1.72  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.82/1.72  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.82/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.82/1.72  
% 3.82/1.74  tff(f_112, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((C = D) => (v2_compts_1(C, A) <=> v2_compts_1(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_compts_1)).
% 3.82/1.74  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.82/1.74  tff(f_68, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 3.82/1.74  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 3.82/1.74  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 3.82/1.74  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, k2_struct_0(B)) => (v2_compts_1(C, A) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((D = C) => v2_compts_1(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_compts_1)).
% 3.82/1.74  tff(c_56, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.82/1.74  tff(c_54, plain, (m1_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.82/1.74  tff(c_74, plain, (![B_86, A_87]: (l1_pre_topc(B_86) | ~m1_pre_topc(B_86, A_87) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.82/1.74  tff(c_77, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_74])).
% 3.82/1.74  tff(c_80, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_77])).
% 3.82/1.74  tff(c_50, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.82/1.74  tff(c_94, plain, (![A_90, B_91]: (m1_pre_topc(k1_pre_topc(A_90, B_91), A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.82/1.74  tff(c_98, plain, (m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_50, c_94])).
% 3.82/1.74  tff(c_104, plain, (m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_98])).
% 3.82/1.74  tff(c_38, plain, (![B_52, A_50]: (l1_pre_topc(B_52) | ~m1_pre_topc(B_52, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.82/1.74  tff(c_114, plain, (l1_pre_topc(k1_pre_topc('#skF_6', '#skF_8')) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_104, c_38])).
% 3.82/1.74  tff(c_117, plain, (l1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_114])).
% 3.82/1.74  tff(c_81, plain, (![A_88, B_89]: (v1_pre_topc(k1_pre_topc(A_88, B_89)) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.82/1.74  tff(c_87, plain, (v1_pre_topc(k1_pre_topc('#skF_6', '#skF_8')) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_50, c_81])).
% 3.82/1.74  tff(c_93, plain, (v1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_87])).
% 3.82/1.74  tff(c_135, plain, (![A_102, B_103]: (k2_struct_0(k1_pre_topc(A_102, B_103))=B_103 | ~m1_pre_topc(k1_pre_topc(A_102, B_103), A_102) | ~v1_pre_topc(k1_pre_topc(A_102, B_103)) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.82/1.74  tff(c_137, plain, (k2_struct_0(k1_pre_topc('#skF_6', '#skF_8'))='#skF_8' | ~v1_pre_topc(k1_pre_topc('#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_104, c_135])).
% 3.82/1.74  tff(c_142, plain, (k2_struct_0(k1_pre_topc('#skF_6', '#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_50, c_93, c_137])).
% 3.82/1.74  tff(c_24, plain, (![B_30, A_8]: (r1_tarski(k2_struct_0(B_30), k2_struct_0(A_8)) | ~m1_pre_topc(B_30, A_8) | ~l1_pre_topc(B_30) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.82/1.74  tff(c_160, plain, (![A_8]: (r1_tarski('#skF_8', k2_struct_0(A_8)) | ~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), A_8) | ~l1_pre_topc(k1_pre_topc('#skF_6', '#skF_8')) | ~l1_pre_topc(A_8))), inference(superposition, [status(thm), theory('equality')], [c_142, c_24])).
% 3.82/1.74  tff(c_177, plain, (![A_8]: (r1_tarski('#skF_8', k2_struct_0(A_8)) | ~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), A_8) | ~l1_pre_topc(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_160])).
% 3.82/1.74  tff(c_48, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.82/1.74  tff(c_58, plain, (~v2_compts_1('#skF_8', '#skF_6') | ~v2_compts_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.82/1.74  tff(c_65, plain, (~v2_compts_1('#skF_8', '#skF_6') | ~v2_compts_1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_58])).
% 3.82/1.74  tff(c_72, plain, (~v2_compts_1('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_65])).
% 3.82/1.74  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.82/1.74  tff(c_66, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52])).
% 3.82/1.74  tff(c_64, plain, (v2_compts_1('#skF_7', '#skF_5') | v2_compts_1('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.82/1.74  tff(c_67, plain, (v2_compts_1('#skF_8', '#skF_5') | v2_compts_1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_64])).
% 3.82/1.74  tff(c_73, plain, (v2_compts_1('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_72, c_67])).
% 3.82/1.74  tff(c_270, plain, (![A_114]: (r1_tarski('#skF_8', k2_struct_0(A_114)) | ~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), A_114) | ~l1_pre_topc(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_160])).
% 3.82/1.74  tff(c_44, plain, (![A_53, B_65, C_71]: ('#skF_4'(A_53, B_65, C_71)=C_71 | v2_compts_1(C_71, A_53) | ~r1_tarski(C_71, k2_struct_0(B_65)) | ~m1_subset_1(C_71, k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_pre_topc(B_65, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.82/1.74  tff(c_606, plain, (![A_167, A_168]: ('#skF_4'(A_167, A_168, '#skF_8')='#skF_8' | v2_compts_1('#skF_8', A_167) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0(A_167))) | ~m1_pre_topc(A_168, A_167) | ~l1_pre_topc(A_167) | ~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), A_168) | ~l1_pre_topc(A_168))), inference(resolution, [status(thm)], [c_270, c_44])).
% 3.82/1.74  tff(c_608, plain, (![A_168]: ('#skF_4'('#skF_5', A_168, '#skF_8')='#skF_8' | v2_compts_1('#skF_8', '#skF_5') | ~m1_pre_topc(A_168, '#skF_5') | ~l1_pre_topc('#skF_5') | ~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), A_168) | ~l1_pre_topc(A_168))), inference(resolution, [status(thm)], [c_66, c_606])).
% 3.82/1.74  tff(c_613, plain, (![A_168]: ('#skF_4'('#skF_5', A_168, '#skF_8')='#skF_8' | v2_compts_1('#skF_8', '#skF_5') | ~m1_pre_topc(A_168, '#skF_5') | ~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), A_168) | ~l1_pre_topc(A_168))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_608])).
% 3.82/1.74  tff(c_618, plain, (![A_169]: ('#skF_4'('#skF_5', A_169, '#skF_8')='#skF_8' | ~m1_pre_topc(A_169, '#skF_5') | ~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), A_169) | ~l1_pre_topc(A_169))), inference(negUnitSimplification, [status(thm)], [c_72, c_613])).
% 3.82/1.74  tff(c_621, plain, ('#skF_4'('#skF_5', '#skF_6', '#skF_8')='#skF_8' | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_104, c_618])).
% 3.82/1.74  tff(c_624, plain, ('#skF_4'('#skF_5', '#skF_6', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_54, c_621])).
% 3.82/1.74  tff(c_42, plain, (![A_53, B_65, C_71]: (~v2_compts_1('#skF_4'(A_53, B_65, C_71), B_65) | v2_compts_1(C_71, A_53) | ~r1_tarski(C_71, k2_struct_0(B_65)) | ~m1_subset_1(C_71, k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_pre_topc(B_65, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.82/1.74  tff(c_630, plain, (~v2_compts_1('#skF_8', '#skF_6') | v2_compts_1('#skF_8', '#skF_5') | ~r1_tarski('#skF_8', k2_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_624, c_42])).
% 3.82/1.74  tff(c_637, plain, (v2_compts_1('#skF_8', '#skF_5') | ~r1_tarski('#skF_8', k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_66, c_73, c_630])).
% 3.82/1.74  tff(c_638, plain, (~r1_tarski('#skF_8', k2_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_637])).
% 3.82/1.74  tff(c_645, plain, (~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_177, c_638])).
% 3.82/1.74  tff(c_652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_104, c_645])).
% 3.82/1.74  tff(c_654, plain, (v2_compts_1('#skF_8', '#skF_5')), inference(splitRight, [status(thm)], [c_65])).
% 3.82/1.74  tff(c_657, plain, (![B_170, A_171]: (l1_pre_topc(B_170) | ~m1_pre_topc(B_170, A_171) | ~l1_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.82/1.74  tff(c_660, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_657])).
% 3.82/1.74  tff(c_663, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_660])).
% 3.82/1.74  tff(c_678, plain, (![A_176, B_177]: (m1_pre_topc(k1_pre_topc(A_176, B_177), A_176) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.82/1.74  tff(c_682, plain, (m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_50, c_678])).
% 3.82/1.74  tff(c_688, plain, (m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_663, c_682])).
% 3.82/1.74  tff(c_697, plain, (l1_pre_topc(k1_pre_topc('#skF_6', '#skF_8')) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_688, c_38])).
% 3.82/1.74  tff(c_700, plain, (l1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_663, c_697])).
% 3.82/1.74  tff(c_664, plain, (![A_172, B_173]: (v1_pre_topc(k1_pre_topc(A_172, B_173)) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.82/1.74  tff(c_674, plain, (v1_pre_topc(k1_pre_topc('#skF_6', '#skF_8')) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_50, c_664])).
% 3.82/1.74  tff(c_676, plain, (v1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_663, c_674])).
% 3.82/1.74  tff(c_718, plain, (![A_186, B_187]: (k2_struct_0(k1_pre_topc(A_186, B_187))=B_187 | ~m1_pre_topc(k1_pre_topc(A_186, B_187), A_186) | ~v1_pre_topc(k1_pre_topc(A_186, B_187)) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(A_186))) | ~l1_pre_topc(A_186))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.82/1.74  tff(c_720, plain, (k2_struct_0(k1_pre_topc('#skF_6', '#skF_8'))='#skF_8' | ~v1_pre_topc(k1_pre_topc('#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_688, c_718])).
% 3.82/1.74  tff(c_725, plain, (k2_struct_0(k1_pre_topc('#skF_6', '#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_663, c_50, c_676, c_720])).
% 3.82/1.74  tff(c_743, plain, (![A_8]: (r1_tarski('#skF_8', k2_struct_0(A_8)) | ~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), A_8) | ~l1_pre_topc(k1_pre_topc('#skF_6', '#skF_8')) | ~l1_pre_topc(A_8))), inference(superposition, [status(thm), theory('equality')], [c_725, c_24])).
% 3.82/1.74  tff(c_760, plain, (![A_8]: (r1_tarski('#skF_8', k2_struct_0(A_8)) | ~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), A_8) | ~l1_pre_topc(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_700, c_743])).
% 3.82/1.74  tff(c_653, plain, (~v2_compts_1('#skF_8', '#skF_6')), inference(splitRight, [status(thm)], [c_65])).
% 3.82/1.74  tff(c_1031, plain, (![D_231, B_232, A_233]: (v2_compts_1(D_231, B_232) | ~m1_subset_1(D_231, k1_zfmisc_1(u1_struct_0(B_232))) | ~v2_compts_1(D_231, A_233) | ~r1_tarski(D_231, k2_struct_0(B_232)) | ~m1_subset_1(D_231, k1_zfmisc_1(u1_struct_0(A_233))) | ~m1_pre_topc(B_232, A_233) | ~l1_pre_topc(A_233))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.82/1.74  tff(c_1041, plain, (![A_233]: (v2_compts_1('#skF_8', '#skF_6') | ~v2_compts_1('#skF_8', A_233) | ~r1_tarski('#skF_8', k2_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0(A_233))) | ~m1_pre_topc('#skF_6', A_233) | ~l1_pre_topc(A_233))), inference(resolution, [status(thm)], [c_50, c_1031])).
% 3.82/1.74  tff(c_1049, plain, (![A_233]: (~v2_compts_1('#skF_8', A_233) | ~r1_tarski('#skF_8', k2_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0(A_233))) | ~m1_pre_topc('#skF_6', A_233) | ~l1_pre_topc(A_233))), inference(negUnitSimplification, [status(thm)], [c_653, c_1041])).
% 3.82/1.74  tff(c_1050, plain, (~r1_tarski('#skF_8', k2_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_1049])).
% 3.82/1.74  tff(c_1056, plain, (~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_760, c_1050])).
% 3.82/1.74  tff(c_1063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_663, c_688, c_1056])).
% 3.82/1.74  tff(c_1069, plain, (![A_234]: (~v2_compts_1('#skF_8', A_234) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0(A_234))) | ~m1_pre_topc('#skF_6', A_234) | ~l1_pre_topc(A_234))), inference(splitRight, [status(thm)], [c_1049])).
% 3.82/1.74  tff(c_1072, plain, (~v2_compts_1('#skF_8', '#skF_5') | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1069])).
% 3.82/1.74  tff(c_1079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_654, c_1072])).
% 3.82/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.74  
% 3.82/1.74  Inference rules
% 3.82/1.74  ----------------------
% 3.82/1.74  #Ref     : 0
% 3.82/1.74  #Sup     : 205
% 3.82/1.74  #Fact    : 0
% 3.82/1.74  #Define  : 0
% 3.82/1.74  #Split   : 22
% 3.82/1.74  #Chain   : 0
% 3.82/1.74  #Close   : 0
% 3.82/1.74  
% 3.82/1.74  Ordering : KBO
% 3.82/1.74  
% 3.82/1.74  Simplification rules
% 3.82/1.74  ----------------------
% 3.82/1.74  #Subsume      : 18
% 3.82/1.74  #Demod        : 156
% 3.82/1.74  #Tautology    : 34
% 3.82/1.74  #SimpNegUnit  : 15
% 3.82/1.74  #BackRed      : 0
% 3.82/1.74  
% 3.82/1.74  #Partial instantiations: 0
% 3.82/1.74  #Strategies tried      : 1
% 3.82/1.74  
% 3.82/1.74  Timing (in seconds)
% 3.82/1.74  ----------------------
% 3.82/1.74  Preprocessing        : 0.39
% 3.82/1.74  Parsing              : 0.18
% 3.82/1.74  CNF conversion       : 0.03
% 3.82/1.74  Main loop            : 0.51
% 3.82/1.74  Inferencing          : 0.18
% 3.82/1.74  Reduction            : 0.16
% 3.82/1.74  Demodulation         : 0.11
% 3.82/1.74  BG Simplification    : 0.03
% 3.82/1.74  Subsumption          : 0.11
% 3.82/1.74  Abstraction          : 0.02
% 3.82/1.74  MUC search           : 0.00
% 3.82/1.74  Cooper               : 0.00
% 3.82/1.74  Total                : 0.93
% 3.82/1.74  Index Insertion      : 0.00
% 3.82/1.74  Index Deletion       : 0.00
% 3.82/1.74  Index Matching       : 0.00
% 3.82/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
