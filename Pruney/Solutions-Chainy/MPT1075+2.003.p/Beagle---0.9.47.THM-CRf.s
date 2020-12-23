%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:10 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 230 expanded)
%              Number of leaves         :   33 (  97 expanded)
%              Depth                    :   13
%              Number of atoms          :  242 ( 979 expanded)
%              Number of equality atoms :   44 ( 139 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                   => ! [F] :
                        ( m1_subset_1(F,B)
                       => ( v1_partfun1(E,A)
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k1_funct_1(E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C,D,E] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k8_funct_2(A,B,C,D,E))
        & v1_funct_2(k8_funct_2(A,B,C,D,E),A,C)
        & m1_subset_1(k8_funct_2(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_40,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_76,plain,(
    ! [C_76,A_77,B_78] :
      ( ~ v1_partfun1(C_76,A_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_xboole_0(B_78)
      | v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_86,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_76])).

tff(c_92,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_86])).

tff(c_93,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_92])).

tff(c_42,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_108,plain,(
    ! [A_83,B_84,C_85] :
      ( m1_subset_1(k2_relset_1(A_83,B_84,C_85),k1_zfmisc_1(B_84))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_118,plain,(
    ! [A_86,B_87,C_88] :
      ( r1_tarski(k2_relset_1(A_86,B_87,C_88),B_87)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(resolution,[status(thm)],[c_108,c_4])).

tff(c_131,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_118])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_190,plain,(
    ! [C_104,A_105,B_106] :
      ( v1_funct_2(C_104,A_105,B_106)
      | ~ v1_partfun1(C_104,A_105)
      | ~ v1_funct_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_204,plain,
    ( v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_190])).

tff(c_212,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_204])).

tff(c_252,plain,(
    ! [B_113,A_114,C_115] :
      ( k1_xboole_0 = B_113
      | k1_relset_1(A_114,B_113,C_115) = A_114
      | ~ v1_funct_2(C_115,A_114,B_113)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_114,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_266,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_252])).

tff(c_274,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_266])).

tff(c_280,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_766,plain,(
    ! [C_234,A_232,D_237,E_236,B_235,F_233] :
      ( k1_funct_1(k8_funct_2(B_235,C_234,A_232,D_237,E_236),F_233) = k1_funct_1(E_236,k1_funct_1(D_237,F_233))
      | k1_xboole_0 = B_235
      | ~ r1_tarski(k2_relset_1(B_235,C_234,D_237),k1_relset_1(C_234,A_232,E_236))
      | ~ m1_subset_1(F_233,B_235)
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(C_234,A_232)))
      | ~ v1_funct_1(E_236)
      | ~ m1_subset_1(D_237,k1_zfmisc_1(k2_zfmisc_1(B_235,C_234)))
      | ~ v1_funct_2(D_237,B_235,C_234)
      | ~ v1_funct_1(D_237)
      | v1_xboole_0(C_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_768,plain,(
    ! [B_235,D_237,F_233] :
      ( k1_funct_1(k8_funct_2(B_235,'#skF_1','#skF_3',D_237,'#skF_5'),F_233) = k1_funct_1('#skF_5',k1_funct_1(D_237,F_233))
      | k1_xboole_0 = B_235
      | ~ r1_tarski(k2_relset_1(B_235,'#skF_1',D_237),'#skF_1')
      | ~ m1_subset_1(F_233,B_235)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_237,k1_zfmisc_1(k2_zfmisc_1(B_235,'#skF_1')))
      | ~ v1_funct_2(D_237,B_235,'#skF_1')
      | ~ v1_funct_1(D_237)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_766])).

tff(c_772,plain,(
    ! [B_235,D_237,F_233] :
      ( k1_funct_1(k8_funct_2(B_235,'#skF_1','#skF_3',D_237,'#skF_5'),F_233) = k1_funct_1('#skF_5',k1_funct_1(D_237,F_233))
      | k1_xboole_0 = B_235
      | ~ r1_tarski(k2_relset_1(B_235,'#skF_1',D_237),'#skF_1')
      | ~ m1_subset_1(F_233,B_235)
      | ~ m1_subset_1(D_237,k1_zfmisc_1(k2_zfmisc_1(B_235,'#skF_1')))
      | ~ v1_funct_2(D_237,B_235,'#skF_1')
      | ~ v1_funct_1(D_237)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_768])).

tff(c_1020,plain,(
    ! [B_292,D_293,F_294] :
      ( k1_funct_1(k8_funct_2(B_292,'#skF_1','#skF_3',D_293,'#skF_5'),F_294) = k1_funct_1('#skF_5',k1_funct_1(D_293,F_294))
      | k1_xboole_0 = B_292
      | ~ r1_tarski(k2_relset_1(B_292,'#skF_1',D_293),'#skF_1')
      | ~ m1_subset_1(F_294,B_292)
      | ~ m1_subset_1(D_293,k1_zfmisc_1(k2_zfmisc_1(B_292,'#skF_1')))
      | ~ v1_funct_2(D_293,B_292,'#skF_1')
      | ~ v1_funct_1(D_293) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_772])).

tff(c_1031,plain,(
    ! [F_294] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_294) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_294))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_294,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_1020])).

tff(c_1037,plain,(
    ! [F_294] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_294) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_294))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_294,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_131,c_1031])).

tff(c_1038,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1037])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1065,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_2])).

tff(c_1067,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1065])).

tff(c_1068,plain,(
    ! [F_294] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_294) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_294))
      | ~ m1_subset_1(F_294,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_1037])).

tff(c_431,plain,(
    ! [E_152,C_155,A_153,B_151,D_154] :
      ( v1_funct_1(k8_funct_2(A_153,B_151,C_155,D_154,E_152))
      | ~ m1_subset_1(E_152,k1_zfmisc_1(k2_zfmisc_1(B_151,C_155)))
      | ~ v1_funct_1(E_152)
      | ~ m1_subset_1(D_154,k1_zfmisc_1(k2_zfmisc_1(A_153,B_151)))
      | ~ v1_funct_2(D_154,A_153,B_151)
      | ~ v1_funct_1(D_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_441,plain,(
    ! [A_153,D_154] :
      ( v1_funct_1(k8_funct_2(A_153,'#skF_1','#skF_3',D_154,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_154,k1_zfmisc_1(k2_zfmisc_1(A_153,'#skF_1')))
      | ~ v1_funct_2(D_154,A_153,'#skF_1')
      | ~ v1_funct_1(D_154) ) ),
    inference(resolution,[status(thm)],[c_44,c_431])).

tff(c_472,plain,(
    ! [A_160,D_161] :
      ( v1_funct_1(k8_funct_2(A_160,'#skF_1','#skF_3',D_161,'#skF_5'))
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(A_160,'#skF_1')))
      | ~ v1_funct_2(D_161,A_160,'#skF_1')
      | ~ v1_funct_1(D_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_441])).

tff(c_483,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_472])).

tff(c_488,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_483])).

tff(c_543,plain,(
    ! [B_171,D_174,C_175,A_173,E_172] :
      ( v1_funct_2(k8_funct_2(A_173,B_171,C_175,D_174,E_172),A_173,C_175)
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(B_171,C_175)))
      | ~ v1_funct_1(E_172)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(A_173,B_171)))
      | ~ v1_funct_2(D_174,A_173,B_171)
      | ~ v1_funct_1(D_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_553,plain,(
    ! [A_173,D_174] :
      ( v1_funct_2(k8_funct_2(A_173,'#skF_1','#skF_3',D_174,'#skF_5'),A_173,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(A_173,'#skF_1')))
      | ~ v1_funct_2(D_174,A_173,'#skF_1')
      | ~ v1_funct_1(D_174) ) ),
    inference(resolution,[status(thm)],[c_44,c_543])).

tff(c_583,plain,(
    ! [A_182,D_183] :
      ( v1_funct_2(k8_funct_2(A_182,'#skF_1','#skF_3',D_183,'#skF_5'),A_182,'#skF_3')
      | ~ m1_subset_1(D_183,k1_zfmisc_1(k2_zfmisc_1(A_182,'#skF_1')))
      | ~ v1_funct_2(D_183,A_182,'#skF_1')
      | ~ v1_funct_1(D_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_553])).

tff(c_591,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_583])).

tff(c_596,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_591])).

tff(c_623,plain,(
    ! [E_198,D_200,B_197,C_201,A_199] :
      ( m1_subset_1(k8_funct_2(A_199,B_197,C_201,D_200,E_198),k1_zfmisc_1(k2_zfmisc_1(A_199,C_201)))
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(B_197,C_201)))
      | ~ v1_funct_1(E_198)
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(A_199,B_197)))
      | ~ v1_funct_2(D_200,A_199,B_197)
      | ~ v1_funct_1(D_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_359,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( k3_funct_2(A_134,B_135,C_136,D_137) = k1_funct_1(C_136,D_137)
      | ~ m1_subset_1(D_137,A_134)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_2(C_136,A_134,B_135)
      | ~ v1_funct_1(C_136)
      | v1_xboole_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_369,plain,(
    ! [B_135,C_136] :
      ( k3_funct_2('#skF_2',B_135,C_136,'#skF_6') = k1_funct_1(C_136,'#skF_6')
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_135)))
      | ~ v1_funct_2(C_136,'#skF_2',B_135)
      | ~ v1_funct_1(C_136)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_359])).

tff(c_376,plain,(
    ! [B_135,C_136] :
      ( k3_funct_2('#skF_2',B_135,C_136,'#skF_6') = k1_funct_1(C_136,'#skF_6')
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_135)))
      | ~ v1_funct_2(C_136,'#skF_2',B_135)
      | ~ v1_funct_1(C_136) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_369])).

tff(c_1435,plain,(
    ! [C_351,B_352,D_353,E_354] :
      ( k3_funct_2('#skF_2',C_351,k8_funct_2('#skF_2',B_352,C_351,D_353,E_354),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2',B_352,C_351,D_353,E_354),'#skF_6')
      | ~ v1_funct_2(k8_funct_2('#skF_2',B_352,C_351,D_353,E_354),'#skF_2',C_351)
      | ~ v1_funct_1(k8_funct_2('#skF_2',B_352,C_351,D_353,E_354))
      | ~ m1_subset_1(E_354,k1_zfmisc_1(k2_zfmisc_1(B_352,C_351)))
      | ~ v1_funct_1(E_354)
      | ~ m1_subset_1(D_353,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_352)))
      | ~ v1_funct_2(D_353,'#skF_2',B_352)
      | ~ v1_funct_1(D_353) ) ),
    inference(resolution,[status(thm)],[c_623,c_376])).

tff(c_1445,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_596,c_1435])).

tff(c_1458,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_488,c_1445])).

tff(c_377,plain,(
    ! [B_138,C_139] :
      ( k3_funct_2('#skF_2',B_138,C_139,'#skF_6') = k1_funct_1(C_139,'#skF_6')
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_138)))
      | ~ v1_funct_2(C_139,'#skF_2',B_138)
      | ~ v1_funct_1(C_139) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_369])).

tff(c_388,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_377])).

tff(c_393,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_388])).

tff(c_38,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_394,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_38])).

tff(c_1462,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_394])).

tff(c_1469,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_1462])).

tff(c_1473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1469])).

tff(c_1474,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_1486,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1474,c_2])).

tff(c_1488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_1486])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:29:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.88  
% 4.74/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.89  %$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.74/1.89  
% 4.74/1.89  %Foreground sorts:
% 4.74/1.89  
% 4.74/1.89  
% 4.74/1.89  %Background operators:
% 4.74/1.89  
% 4.74/1.89  
% 4.74/1.89  %Foreground operators:
% 4.74/1.89  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.74/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.74/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.74/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.74/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.74/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.74/1.89  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.74/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.74/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.74/1.89  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.74/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.74/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.74/1.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.74/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.74/1.89  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.74/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.74/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.74/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.74/1.89  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.74/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.74/1.89  
% 5.05/1.92  tff(f_153, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_funct_2)).
% 5.05/1.92  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_partfun1)).
% 5.05/1.92  tff(f_34, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.05/1.92  tff(f_30, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.05/1.92  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 5.05/1.92  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.05/1.92  tff(f_126, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 5.05/1.92  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.05/1.92  tff(f_89, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 5.05/1.92  tff(f_102, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 5.05/1.92  tff(c_56, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.05/1.92  tff(c_40, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.05/1.92  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.05/1.92  tff(c_76, plain, (![C_76, A_77, B_78]: (~v1_partfun1(C_76, A_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_xboole_0(B_78) | v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.05/1.92  tff(c_86, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_76])).
% 5.05/1.92  tff(c_92, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_86])).
% 5.05/1.92  tff(c_93, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_92])).
% 5.05/1.92  tff(c_42, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.05/1.92  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.05/1.92  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.05/1.92  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.05/1.92  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.05/1.92  tff(c_108, plain, (![A_83, B_84, C_85]: (m1_subset_1(k2_relset_1(A_83, B_84, C_85), k1_zfmisc_1(B_84)) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.05/1.92  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.05/1.92  tff(c_118, plain, (![A_86, B_87, C_88]: (r1_tarski(k2_relset_1(A_86, B_87, C_88), B_87) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(resolution, [status(thm)], [c_108, c_4])).
% 5.05/1.92  tff(c_131, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_1', '#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_48, c_118])).
% 5.05/1.92  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.05/1.92  tff(c_190, plain, (![C_104, A_105, B_106]: (v1_funct_2(C_104, A_105, B_106) | ~v1_partfun1(C_104, A_105) | ~v1_funct_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.05/1.92  tff(c_204, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_190])).
% 5.05/1.92  tff(c_212, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_204])).
% 5.05/1.92  tff(c_252, plain, (![B_113, A_114, C_115]: (k1_xboole_0=B_113 | k1_relset_1(A_114, B_113, C_115)=A_114 | ~v1_funct_2(C_115, A_114, B_113) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_114, B_113))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.05/1.92  tff(c_266, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_252])).
% 5.05/1.92  tff(c_274, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_212, c_266])).
% 5.05/1.92  tff(c_280, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_274])).
% 5.05/1.92  tff(c_766, plain, (![C_234, A_232, D_237, E_236, B_235, F_233]: (k1_funct_1(k8_funct_2(B_235, C_234, A_232, D_237, E_236), F_233)=k1_funct_1(E_236, k1_funct_1(D_237, F_233)) | k1_xboole_0=B_235 | ~r1_tarski(k2_relset_1(B_235, C_234, D_237), k1_relset_1(C_234, A_232, E_236)) | ~m1_subset_1(F_233, B_235) | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1(C_234, A_232))) | ~v1_funct_1(E_236) | ~m1_subset_1(D_237, k1_zfmisc_1(k2_zfmisc_1(B_235, C_234))) | ~v1_funct_2(D_237, B_235, C_234) | ~v1_funct_1(D_237) | v1_xboole_0(C_234))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.05/1.92  tff(c_768, plain, (![B_235, D_237, F_233]: (k1_funct_1(k8_funct_2(B_235, '#skF_1', '#skF_3', D_237, '#skF_5'), F_233)=k1_funct_1('#skF_5', k1_funct_1(D_237, F_233)) | k1_xboole_0=B_235 | ~r1_tarski(k2_relset_1(B_235, '#skF_1', D_237), '#skF_1') | ~m1_subset_1(F_233, B_235) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_237, k1_zfmisc_1(k2_zfmisc_1(B_235, '#skF_1'))) | ~v1_funct_2(D_237, B_235, '#skF_1') | ~v1_funct_1(D_237) | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_280, c_766])).
% 5.05/1.92  tff(c_772, plain, (![B_235, D_237, F_233]: (k1_funct_1(k8_funct_2(B_235, '#skF_1', '#skF_3', D_237, '#skF_5'), F_233)=k1_funct_1('#skF_5', k1_funct_1(D_237, F_233)) | k1_xboole_0=B_235 | ~r1_tarski(k2_relset_1(B_235, '#skF_1', D_237), '#skF_1') | ~m1_subset_1(F_233, B_235) | ~m1_subset_1(D_237, k1_zfmisc_1(k2_zfmisc_1(B_235, '#skF_1'))) | ~v1_funct_2(D_237, B_235, '#skF_1') | ~v1_funct_1(D_237) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_768])).
% 5.05/1.92  tff(c_1020, plain, (![B_292, D_293, F_294]: (k1_funct_1(k8_funct_2(B_292, '#skF_1', '#skF_3', D_293, '#skF_5'), F_294)=k1_funct_1('#skF_5', k1_funct_1(D_293, F_294)) | k1_xboole_0=B_292 | ~r1_tarski(k2_relset_1(B_292, '#skF_1', D_293), '#skF_1') | ~m1_subset_1(F_294, B_292) | ~m1_subset_1(D_293, k1_zfmisc_1(k2_zfmisc_1(B_292, '#skF_1'))) | ~v1_funct_2(D_293, B_292, '#skF_1') | ~v1_funct_1(D_293))), inference(negUnitSimplification, [status(thm)], [c_56, c_772])).
% 5.05/1.92  tff(c_1031, plain, (![F_294]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_294)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_294)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relset_1('#skF_2', '#skF_1', '#skF_4'), '#skF_1') | ~m1_subset_1(F_294, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_1020])).
% 5.05/1.92  tff(c_1037, plain, (![F_294]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_294)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_294)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_294, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_131, c_1031])).
% 5.05/1.92  tff(c_1038, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1037])).
% 5.05/1.92  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.05/1.92  tff(c_1065, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1038, c_2])).
% 5.05/1.92  tff(c_1067, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1065])).
% 5.05/1.92  tff(c_1068, plain, (![F_294]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_294)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_294)) | ~m1_subset_1(F_294, '#skF_2'))), inference(splitRight, [status(thm)], [c_1037])).
% 5.05/1.92  tff(c_431, plain, (![E_152, C_155, A_153, B_151, D_154]: (v1_funct_1(k8_funct_2(A_153, B_151, C_155, D_154, E_152)) | ~m1_subset_1(E_152, k1_zfmisc_1(k2_zfmisc_1(B_151, C_155))) | ~v1_funct_1(E_152) | ~m1_subset_1(D_154, k1_zfmisc_1(k2_zfmisc_1(A_153, B_151))) | ~v1_funct_2(D_154, A_153, B_151) | ~v1_funct_1(D_154))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.05/1.92  tff(c_441, plain, (![A_153, D_154]: (v1_funct_1(k8_funct_2(A_153, '#skF_1', '#skF_3', D_154, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_154, k1_zfmisc_1(k2_zfmisc_1(A_153, '#skF_1'))) | ~v1_funct_2(D_154, A_153, '#skF_1') | ~v1_funct_1(D_154))), inference(resolution, [status(thm)], [c_44, c_431])).
% 5.05/1.92  tff(c_472, plain, (![A_160, D_161]: (v1_funct_1(k8_funct_2(A_160, '#skF_1', '#skF_3', D_161, '#skF_5')) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(A_160, '#skF_1'))) | ~v1_funct_2(D_161, A_160, '#skF_1') | ~v1_funct_1(D_161))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_441])).
% 5.05/1.92  tff(c_483, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_472])).
% 5.05/1.92  tff(c_488, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_483])).
% 5.05/1.92  tff(c_543, plain, (![B_171, D_174, C_175, A_173, E_172]: (v1_funct_2(k8_funct_2(A_173, B_171, C_175, D_174, E_172), A_173, C_175) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(B_171, C_175))) | ~v1_funct_1(E_172) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(A_173, B_171))) | ~v1_funct_2(D_174, A_173, B_171) | ~v1_funct_1(D_174))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.05/1.92  tff(c_553, plain, (![A_173, D_174]: (v1_funct_2(k8_funct_2(A_173, '#skF_1', '#skF_3', D_174, '#skF_5'), A_173, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(A_173, '#skF_1'))) | ~v1_funct_2(D_174, A_173, '#skF_1') | ~v1_funct_1(D_174))), inference(resolution, [status(thm)], [c_44, c_543])).
% 5.05/1.92  tff(c_583, plain, (![A_182, D_183]: (v1_funct_2(k8_funct_2(A_182, '#skF_1', '#skF_3', D_183, '#skF_5'), A_182, '#skF_3') | ~m1_subset_1(D_183, k1_zfmisc_1(k2_zfmisc_1(A_182, '#skF_1'))) | ~v1_funct_2(D_183, A_182, '#skF_1') | ~v1_funct_1(D_183))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_553])).
% 5.05/1.92  tff(c_591, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_583])).
% 5.05/1.92  tff(c_596, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_591])).
% 5.05/1.92  tff(c_623, plain, (![E_198, D_200, B_197, C_201, A_199]: (m1_subset_1(k8_funct_2(A_199, B_197, C_201, D_200, E_198), k1_zfmisc_1(k2_zfmisc_1(A_199, C_201))) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(B_197, C_201))) | ~v1_funct_1(E_198) | ~m1_subset_1(D_200, k1_zfmisc_1(k2_zfmisc_1(A_199, B_197))) | ~v1_funct_2(D_200, A_199, B_197) | ~v1_funct_1(D_200))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.05/1.92  tff(c_359, plain, (![A_134, B_135, C_136, D_137]: (k3_funct_2(A_134, B_135, C_136, D_137)=k1_funct_1(C_136, D_137) | ~m1_subset_1(D_137, A_134) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_2(C_136, A_134, B_135) | ~v1_funct_1(C_136) | v1_xboole_0(A_134))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.05/1.92  tff(c_369, plain, (![B_135, C_136]: (k3_funct_2('#skF_2', B_135, C_136, '#skF_6')=k1_funct_1(C_136, '#skF_6') | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_135))) | ~v1_funct_2(C_136, '#skF_2', B_135) | ~v1_funct_1(C_136) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_359])).
% 5.05/1.92  tff(c_376, plain, (![B_135, C_136]: (k3_funct_2('#skF_2', B_135, C_136, '#skF_6')=k1_funct_1(C_136, '#skF_6') | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_135))) | ~v1_funct_2(C_136, '#skF_2', B_135) | ~v1_funct_1(C_136))), inference(negUnitSimplification, [status(thm)], [c_54, c_369])).
% 5.05/1.92  tff(c_1435, plain, (![C_351, B_352, D_353, E_354]: (k3_funct_2('#skF_2', C_351, k8_funct_2('#skF_2', B_352, C_351, D_353, E_354), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', B_352, C_351, D_353, E_354), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', B_352, C_351, D_353, E_354), '#skF_2', C_351) | ~v1_funct_1(k8_funct_2('#skF_2', B_352, C_351, D_353, E_354)) | ~m1_subset_1(E_354, k1_zfmisc_1(k2_zfmisc_1(B_352, C_351))) | ~v1_funct_1(E_354) | ~m1_subset_1(D_353, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_352))) | ~v1_funct_2(D_353, '#skF_2', B_352) | ~v1_funct_1(D_353))), inference(resolution, [status(thm)], [c_623, c_376])).
% 5.05/1.92  tff(c_1445, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_596, c_1435])).
% 5.05/1.92  tff(c_1458, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_488, c_1445])).
% 5.05/1.92  tff(c_377, plain, (![B_138, C_139]: (k3_funct_2('#skF_2', B_138, C_139, '#skF_6')=k1_funct_1(C_139, '#skF_6') | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_138))) | ~v1_funct_2(C_139, '#skF_2', B_138) | ~v1_funct_1(C_139))), inference(negUnitSimplification, [status(thm)], [c_54, c_369])).
% 5.05/1.92  tff(c_388, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_377])).
% 5.05/1.92  tff(c_393, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_388])).
% 5.05/1.92  tff(c_38, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.05/1.92  tff(c_394, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_38])).
% 5.05/1.92  tff(c_1462, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_394])).
% 5.05/1.92  tff(c_1469, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1068, c_1462])).
% 5.05/1.92  tff(c_1473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1469])).
% 5.05/1.92  tff(c_1474, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_274])).
% 5.05/1.92  tff(c_1486, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1474, c_2])).
% 5.05/1.92  tff(c_1488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_1486])).
% 5.05/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.92  
% 5.05/1.92  Inference rules
% 5.05/1.92  ----------------------
% 5.05/1.92  #Ref     : 0
% 5.05/1.92  #Sup     : 272
% 5.05/1.92  #Fact    : 0
% 5.05/1.92  #Define  : 0
% 5.05/1.92  #Split   : 6
% 5.05/1.92  #Chain   : 0
% 5.05/1.92  #Close   : 0
% 5.05/1.92  
% 5.05/1.92  Ordering : KBO
% 5.05/1.92  
% 5.05/1.92  Simplification rules
% 5.05/1.93  ----------------------
% 5.05/1.93  #Subsume      : 23
% 5.05/1.93  #Demod        : 335
% 5.05/1.93  #Tautology    : 36
% 5.05/1.93  #SimpNegUnit  : 13
% 5.05/1.93  #BackRed      : 74
% 5.05/1.93  
% 5.05/1.93  #Partial instantiations: 0
% 5.05/1.93  #Strategies tried      : 1
% 5.05/1.93  
% 5.05/1.93  Timing (in seconds)
% 5.05/1.93  ----------------------
% 5.05/1.93  Preprocessing        : 0.35
% 5.05/1.93  Parsing              : 0.18
% 5.05/1.93  CNF conversion       : 0.03
% 5.05/1.93  Main loop            : 0.72
% 5.05/1.93  Inferencing          : 0.26
% 5.05/1.93  Reduction            : 0.22
% 5.05/1.93  Demodulation         : 0.15
% 5.05/1.93  BG Simplification    : 0.04
% 5.05/1.93  Subsumption          : 0.14
% 5.05/1.93  Abstraction          : 0.05
% 5.05/1.93  MUC search           : 0.00
% 5.05/1.93  Cooper               : 0.00
% 5.05/1.93  Total                : 1.14
% 5.05/1.93  Index Insertion      : 0.00
% 5.05/1.93  Index Deletion       : 0.00
% 5.05/1.93  Index Matching       : 0.00
% 5.05/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
