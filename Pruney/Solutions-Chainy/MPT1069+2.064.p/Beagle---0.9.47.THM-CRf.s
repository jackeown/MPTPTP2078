%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:54 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 311 expanded)
%              Number of leaves         :   43 ( 128 expanded)
%              Depth                    :   12
%              Number of atoms          :  212 (1062 expanded)
%              Number of equality atoms :   50 ( 253 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C] :
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
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_127,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_92,axiom,(
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

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_50,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_161,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_169,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_161])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_140,plain,(
    ! [A_90,B_91,C_92] :
      ( k2_relset_1(A_90,B_91,C_92) = k2_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_147,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_140])).

tff(c_48,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_149,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_48])).

tff(c_174,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_149])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_838,plain,(
    ! [A_228,B_226,C_227,F_229,D_230,E_225] :
      ( k1_funct_1(k8_funct_2(B_226,C_227,A_228,D_230,E_225),F_229) = k1_funct_1(E_225,k1_funct_1(D_230,F_229))
      | k1_xboole_0 = B_226
      | ~ r1_tarski(k2_relset_1(B_226,C_227,D_230),k1_relset_1(C_227,A_228,E_225))
      | ~ m1_subset_1(F_229,B_226)
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1(C_227,A_228)))
      | ~ v1_funct_1(E_225)
      | ~ m1_subset_1(D_230,k1_zfmisc_1(k2_zfmisc_1(B_226,C_227)))
      | ~ v1_funct_2(D_230,B_226,C_227)
      | ~ v1_funct_1(D_230)
      | v1_xboole_0(C_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_846,plain,(
    ! [A_228,E_225,F_229] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_228,'#skF_5',E_225),F_229) = k1_funct_1(E_225,k1_funct_1('#skF_5',F_229))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',A_228,E_225))
      | ~ m1_subset_1(F_229,'#skF_3')
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_228)))
      | ~ v1_funct_1(E_225)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_838])).

tff(c_855,plain,(
    ! [A_228,E_225,F_229] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_228,'#skF_5',E_225),F_229) = k1_funct_1(E_225,k1_funct_1('#skF_5',F_229))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',A_228,E_225))
      | ~ m1_subset_1(F_229,'#skF_3')
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_228)))
      | ~ v1_funct_1(E_225)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_846])).

tff(c_1298,plain,(
    ! [A_321,E_322,F_323] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_321,'#skF_5',E_322),F_323) = k1_funct_1(E_322,k1_funct_1('#skF_5',F_323))
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',A_321,E_322))
      | ~ m1_subset_1(F_323,'#skF_3')
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_321)))
      | ~ v1_funct_1(E_322) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_46,c_855])).

tff(c_1300,plain,(
    ! [F_323] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_323) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_323))
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_323,'#skF_3')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_1298])).

tff(c_1302,plain,(
    ! [F_323] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_323) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_323))
      | ~ m1_subset_1(F_323,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_174,c_1300])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_84,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_87,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_84])).

tff(c_93,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_87])).

tff(c_168,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_161])).

tff(c_743,plain,(
    ! [B_211,A_212,C_213] :
      ( k1_xboole_0 = B_211
      | k1_relset_1(A_212,B_211,C_213) = A_212
      | ~ v1_funct_2(C_213,A_212,B_211)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_212,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_746,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_743])).

tff(c_752,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_168,c_746])).

tff(c_755,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_752])).

tff(c_782,plain,(
    ! [A_220,B_221,C_222] :
      ( k7_partfun1(A_220,B_221,C_222) = k1_funct_1(B_221,C_222)
      | ~ r2_hidden(C_222,k1_relat_1(B_221))
      | ~ v1_funct_1(B_221)
      | ~ v5_relat_1(B_221,A_220)
      | ~ v1_relat_1(B_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_787,plain,(
    ! [A_220,C_222] :
      ( k7_partfun1(A_220,'#skF_5',C_222) = k1_funct_1('#skF_5',C_222)
      | ~ r2_hidden(C_222,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_220)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_782])).

tff(c_817,plain,(
    ! [A_223,C_224] :
      ( k7_partfun1(A_223,'#skF_5',C_224) = k1_funct_1('#skF_5',C_224)
      | ~ r2_hidden(C_224,'#skF_3')
      | ~ v5_relat_1('#skF_5',A_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_60,c_787])).

tff(c_837,plain,(
    ! [A_223,A_7] :
      ( k7_partfun1(A_223,'#skF_5',A_7) = k1_funct_1('#skF_5',A_7)
      | ~ v5_relat_1('#skF_5',A_223)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_7,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_817])).

tff(c_862,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_837])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_870,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_862,c_10])).

tff(c_874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_870])).

tff(c_876,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_837])).

tff(c_113,plain,(
    ! [C_78,B_79,A_80] :
      ( v5_relat_1(C_78,B_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_121,plain,(
    v5_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_113])).

tff(c_90,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_84])).

tff(c_96,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_90])).

tff(c_699,plain,(
    ! [B_191,A_192] :
      ( r2_hidden(k1_funct_1(B_191,A_192),k2_relat_1(B_191))
      | ~ r2_hidden(A_192,k1_relat_1(B_191))
      | ~ v1_funct_1(B_191)
      | ~ v1_relat_1(B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_702,plain,(
    ! [B_191,A_192,B_2] :
      ( r2_hidden(k1_funct_1(B_191,A_192),B_2)
      | ~ r1_tarski(k2_relat_1(B_191),B_2)
      | ~ r2_hidden(A_192,k1_relat_1(B_191))
      | ~ v1_funct_1(B_191)
      | ~ v1_relat_1(B_191) ) ),
    inference(resolution,[status(thm)],[c_699,c_2])).

tff(c_1423,plain,(
    ! [A_345,B_346,B_347,A_348] :
      ( k7_partfun1(A_345,B_346,k1_funct_1(B_347,A_348)) = k1_funct_1(B_346,k1_funct_1(B_347,A_348))
      | ~ v1_funct_1(B_346)
      | ~ v5_relat_1(B_346,A_345)
      | ~ v1_relat_1(B_346)
      | ~ r1_tarski(k2_relat_1(B_347),k1_relat_1(B_346))
      | ~ r2_hidden(A_348,k1_relat_1(B_347))
      | ~ v1_funct_1(B_347)
      | ~ v1_relat_1(B_347) ) ),
    inference(resolution,[status(thm)],[c_702,c_782])).

tff(c_1427,plain,(
    ! [A_345,A_348] :
      ( k7_partfun1(A_345,'#skF_6',k1_funct_1('#skF_5',A_348)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',A_348))
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_345)
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(A_348,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_174,c_1423])).

tff(c_1433,plain,(
    ! [A_349,A_350] :
      ( k7_partfun1(A_349,'#skF_6',k1_funct_1('#skF_5',A_350)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',A_350))
      | ~ v5_relat_1('#skF_6',A_349)
      | ~ r2_hidden(A_350,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_60,c_755,c_96,c_54,c_1427])).

tff(c_44,plain,(
    k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5','#skF_7')) != k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1439,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ v5_relat_1('#skF_6','#skF_2')
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1433,c_44])).

tff(c_1445,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_1439])).

tff(c_1447,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1445])).

tff(c_1450,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1447])).

tff(c_1453,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1450])).

tff(c_1455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_876,c_1453])).

tff(c_1456,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1445])).

tff(c_1500,plain,(
    ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1302,c_1456])).

tff(c_1504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1500])).

tff(c_1505,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_752])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1513,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1505,c_8])).

tff(c_1516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:29:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.79  
% 4.47/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.79  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.47/1.79  
% 4.47/1.79  %Foreground sorts:
% 4.47/1.79  
% 4.47/1.79  
% 4.47/1.79  %Background operators:
% 4.47/1.79  
% 4.47/1.79  
% 4.47/1.79  %Foreground operators:
% 4.47/1.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.47/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.47/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.47/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.47/1.79  tff('#skF_7', type, '#skF_7': $i).
% 4.47/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.47/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.47/1.79  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.47/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.47/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.47/1.79  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.47/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.47/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.47/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.47/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.47/1.79  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.47/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.47/1.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.47/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.47/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.47/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.47/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.79  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.47/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.47/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.47/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.47/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.47/1.79  
% 4.47/1.81  tff(f_152, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 4.47/1.81  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.47/1.81  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.47/1.81  tff(f_127, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 4.47/1.81  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.47/1.81  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.47/1.81  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.47/1.81  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.47/1.81  tff(f_103, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 4.47/1.81  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.47/1.81  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.47/1.81  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 4.47/1.81  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.47/1.81  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.47/1.81  tff(c_62, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.47/1.81  tff(c_50, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.47/1.81  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.47/1.81  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.47/1.81  tff(c_161, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.47/1.81  tff(c_169, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_161])).
% 4.47/1.81  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.47/1.81  tff(c_140, plain, (![A_90, B_91, C_92]: (k2_relset_1(A_90, B_91, C_92)=k2_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.47/1.81  tff(c_147, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_140])).
% 4.47/1.81  tff(c_48, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.47/1.81  tff(c_149, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_48])).
% 4.47/1.81  tff(c_174, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_149])).
% 4.47/1.81  tff(c_46, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.47/1.81  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.47/1.81  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.47/1.81  tff(c_838, plain, (![A_228, B_226, C_227, F_229, D_230, E_225]: (k1_funct_1(k8_funct_2(B_226, C_227, A_228, D_230, E_225), F_229)=k1_funct_1(E_225, k1_funct_1(D_230, F_229)) | k1_xboole_0=B_226 | ~r1_tarski(k2_relset_1(B_226, C_227, D_230), k1_relset_1(C_227, A_228, E_225)) | ~m1_subset_1(F_229, B_226) | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1(C_227, A_228))) | ~v1_funct_1(E_225) | ~m1_subset_1(D_230, k1_zfmisc_1(k2_zfmisc_1(B_226, C_227))) | ~v1_funct_2(D_230, B_226, C_227) | ~v1_funct_1(D_230) | v1_xboole_0(C_227))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.47/1.81  tff(c_846, plain, (![A_228, E_225, F_229]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_228, '#skF_5', E_225), F_229)=k1_funct_1(E_225, k1_funct_1('#skF_5', F_229)) | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', A_228, E_225)) | ~m1_subset_1(F_229, '#skF_3') | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_228))) | ~v1_funct_1(E_225) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_147, c_838])).
% 4.47/1.81  tff(c_855, plain, (![A_228, E_225, F_229]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_228, '#skF_5', E_225), F_229)=k1_funct_1(E_225, k1_funct_1('#skF_5', F_229)) | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', A_228, E_225)) | ~m1_subset_1(F_229, '#skF_3') | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_228))) | ~v1_funct_1(E_225) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_846])).
% 4.47/1.81  tff(c_1298, plain, (![A_321, E_322, F_323]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_321, '#skF_5', E_322), F_323)=k1_funct_1(E_322, k1_funct_1('#skF_5', F_323)) | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', A_321, E_322)) | ~m1_subset_1(F_323, '#skF_3') | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_321))) | ~v1_funct_1(E_322))), inference(negUnitSimplification, [status(thm)], [c_62, c_46, c_855])).
% 4.47/1.81  tff(c_1300, plain, (![F_323]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_323)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_323)) | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6')) | ~m1_subset_1(F_323, '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_169, c_1298])).
% 4.47/1.81  tff(c_1302, plain, (![F_323]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_323)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_323)) | ~m1_subset_1(F_323, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_174, c_1300])).
% 4.47/1.81  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.47/1.81  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.47/1.81  tff(c_84, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.47/1.81  tff(c_87, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_84])).
% 4.47/1.81  tff(c_93, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_87])).
% 4.47/1.81  tff(c_168, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_161])).
% 4.47/1.81  tff(c_743, plain, (![B_211, A_212, C_213]: (k1_xboole_0=B_211 | k1_relset_1(A_212, B_211, C_213)=A_212 | ~v1_funct_2(C_213, A_212, B_211) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_212, B_211))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.47/1.81  tff(c_746, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_743])).
% 4.47/1.81  tff(c_752, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_168, c_746])).
% 4.47/1.81  tff(c_755, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_752])).
% 4.47/1.81  tff(c_782, plain, (![A_220, B_221, C_222]: (k7_partfun1(A_220, B_221, C_222)=k1_funct_1(B_221, C_222) | ~r2_hidden(C_222, k1_relat_1(B_221)) | ~v1_funct_1(B_221) | ~v5_relat_1(B_221, A_220) | ~v1_relat_1(B_221))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.47/1.81  tff(c_787, plain, (![A_220, C_222]: (k7_partfun1(A_220, '#skF_5', C_222)=k1_funct_1('#skF_5', C_222) | ~r2_hidden(C_222, '#skF_3') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_220) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_755, c_782])).
% 4.47/1.81  tff(c_817, plain, (![A_223, C_224]: (k7_partfun1(A_223, '#skF_5', C_224)=k1_funct_1('#skF_5', C_224) | ~r2_hidden(C_224, '#skF_3') | ~v5_relat_1('#skF_5', A_223))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_60, c_787])).
% 4.47/1.81  tff(c_837, plain, (![A_223, A_7]: (k7_partfun1(A_223, '#skF_5', A_7)=k1_funct_1('#skF_5', A_7) | ~v5_relat_1('#skF_5', A_223) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_7, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_817])).
% 4.47/1.81  tff(c_862, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_837])).
% 4.47/1.81  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.47/1.81  tff(c_870, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_862, c_10])).
% 4.47/1.81  tff(c_874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_870])).
% 4.47/1.81  tff(c_876, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_837])).
% 4.47/1.81  tff(c_113, plain, (![C_78, B_79, A_80]: (v5_relat_1(C_78, B_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.47/1.81  tff(c_121, plain, (v5_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_113])).
% 4.47/1.81  tff(c_90, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_84])).
% 4.47/1.81  tff(c_96, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_90])).
% 4.47/1.81  tff(c_699, plain, (![B_191, A_192]: (r2_hidden(k1_funct_1(B_191, A_192), k2_relat_1(B_191)) | ~r2_hidden(A_192, k1_relat_1(B_191)) | ~v1_funct_1(B_191) | ~v1_relat_1(B_191))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.47/1.81  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.47/1.81  tff(c_702, plain, (![B_191, A_192, B_2]: (r2_hidden(k1_funct_1(B_191, A_192), B_2) | ~r1_tarski(k2_relat_1(B_191), B_2) | ~r2_hidden(A_192, k1_relat_1(B_191)) | ~v1_funct_1(B_191) | ~v1_relat_1(B_191))), inference(resolution, [status(thm)], [c_699, c_2])).
% 4.47/1.81  tff(c_1423, plain, (![A_345, B_346, B_347, A_348]: (k7_partfun1(A_345, B_346, k1_funct_1(B_347, A_348))=k1_funct_1(B_346, k1_funct_1(B_347, A_348)) | ~v1_funct_1(B_346) | ~v5_relat_1(B_346, A_345) | ~v1_relat_1(B_346) | ~r1_tarski(k2_relat_1(B_347), k1_relat_1(B_346)) | ~r2_hidden(A_348, k1_relat_1(B_347)) | ~v1_funct_1(B_347) | ~v1_relat_1(B_347))), inference(resolution, [status(thm)], [c_702, c_782])).
% 4.47/1.81  tff(c_1427, plain, (![A_345, A_348]: (k7_partfun1(A_345, '#skF_6', k1_funct_1('#skF_5', A_348))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', A_348)) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_345) | ~v1_relat_1('#skF_6') | ~r2_hidden(A_348, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_174, c_1423])).
% 4.47/1.81  tff(c_1433, plain, (![A_349, A_350]: (k7_partfun1(A_349, '#skF_6', k1_funct_1('#skF_5', A_350))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', A_350)) | ~v5_relat_1('#skF_6', A_349) | ~r2_hidden(A_350, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_60, c_755, c_96, c_54, c_1427])).
% 4.47/1.81  tff(c_44, plain, (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', '#skF_7'))!=k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.47/1.81  tff(c_1439, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~v5_relat_1('#skF_6', '#skF_2') | ~r2_hidden('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1433, c_44])).
% 4.47/1.81  tff(c_1445, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~r2_hidden('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_1439])).
% 4.47/1.81  tff(c_1447, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_1445])).
% 4.47/1.81  tff(c_1450, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_1447])).
% 4.47/1.81  tff(c_1453, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1450])).
% 4.47/1.81  tff(c_1455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_876, c_1453])).
% 4.47/1.81  tff(c_1456, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_1445])).
% 4.47/1.81  tff(c_1500, plain, (~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1302, c_1456])).
% 4.47/1.81  tff(c_1504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1500])).
% 4.47/1.81  tff(c_1505, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_752])).
% 4.47/1.81  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.47/1.81  tff(c_1513, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1505, c_8])).
% 4.47/1.81  tff(c_1516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1513])).
% 4.47/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.81  
% 4.47/1.81  Inference rules
% 4.47/1.81  ----------------------
% 4.47/1.81  #Ref     : 0
% 4.47/1.81  #Sup     : 309
% 4.47/1.81  #Fact    : 0
% 4.47/1.81  #Define  : 0
% 4.47/1.81  #Split   : 23
% 4.47/1.81  #Chain   : 0
% 4.47/1.81  #Close   : 0
% 4.47/1.81  
% 4.47/1.81  Ordering : KBO
% 4.47/1.81  
% 4.47/1.81  Simplification rules
% 4.47/1.81  ----------------------
% 4.47/1.81  #Subsume      : 65
% 4.47/1.81  #Demod        : 271
% 4.47/1.81  #Tautology    : 74
% 4.47/1.81  #SimpNegUnit  : 25
% 4.47/1.81  #BackRed      : 52
% 4.47/1.81  
% 4.47/1.81  #Partial instantiations: 0
% 4.47/1.81  #Strategies tried      : 1
% 4.47/1.81  
% 4.47/1.81  Timing (in seconds)
% 4.47/1.81  ----------------------
% 4.47/1.82  Preprocessing        : 0.39
% 4.47/1.82  Parsing              : 0.21
% 4.47/1.82  CNF conversion       : 0.03
% 4.47/1.82  Main loop            : 0.63
% 4.47/1.82  Inferencing          : 0.23
% 4.47/1.82  Reduction            : 0.19
% 4.47/1.82  Demodulation         : 0.13
% 4.47/1.82  BG Simplification    : 0.03
% 4.47/1.82  Subsumption          : 0.13
% 4.47/1.82  Abstraction          : 0.03
% 4.47/1.82  MUC search           : 0.00
% 4.47/1.82  Cooper               : 0.00
% 4.47/1.82  Total                : 1.06
% 4.47/1.82  Index Insertion      : 0.00
% 4.47/1.82  Index Deletion       : 0.00
% 4.47/1.82  Index Matching       : 0.00
% 4.47/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
