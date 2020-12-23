%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:39 EST 2020

% Result     : Theorem 13.57s
% Output     : CNFRefutation 13.61s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 218 expanded)
%              Number of leaves         :   34 (  94 expanded)
%              Depth                    :   23
%              Number of atoms          :  283 ( 831 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > v1_funct_1 > k7_funct_2 > k6_funct_2 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k6_funct_2,type,(
    k6_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_funct_2,type,(
    k7_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A)))
                   => r1_tarski(k5_setfam_1(A,D),k5_setfam_1(A,k6_funct_2(A,B,C,k7_funct_2(A,B,C,D)))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_funct_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_120,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A)))
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(A))
                     => ( m1_setfam_1(D,E)
                       => m1_setfam_1(k6_funct_2(A,B,C,k7_funct_2(A,B,C,D)),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A))) )
     => m1_subset_1(k7_funct_2(A,B,C,D),k1_zfmisc_1(k1_zfmisc_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(B))) )
     => m1_subset_1(k6_funct_2(A,B,C,D),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_funct_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_76,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(A_83,B_84)
      | ~ m1_subset_1(A_83,k1_zfmisc_1(B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_88,plain,(
    r1_tarski('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_76])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_3'(A_8,B_9),A_8)
      | r1_tarski(k3_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_128,plain,(
    ! [C_93,A_94,B_95] :
      ( r2_hidden(C_93,A_94)
      | ~ r2_hidden(C_93,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_528,plain,(
    ! [A_177,B_178,A_179] :
      ( r2_hidden('#skF_3'(A_177,B_178),A_179)
      | ~ m1_subset_1(A_177,k1_zfmisc_1(A_179))
      | r1_tarski(k3_tarski(A_177),B_178) ) ),
    inference(resolution,[status(thm)],[c_22,c_128])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_738,plain,(
    ! [A_213,B_214,A_215] :
      ( r1_tarski('#skF_3'(A_213,B_214),A_215)
      | ~ m1_subset_1(A_213,k1_zfmisc_1(k1_zfmisc_1(A_215)))
      | r1_tarski(k3_tarski(A_213),B_214) ) ),
    inference(resolution,[status(thm)],[c_528,c_8])).

tff(c_820,plain,(
    ! [A_221,B_222,A_223] :
      ( r1_tarski('#skF_3'(A_221,B_222),A_223)
      | r1_tarski(k3_tarski(A_221),B_222)
      | ~ r1_tarski(A_221,k1_zfmisc_1(A_223)) ) ),
    inference(resolution,[status(thm)],[c_34,c_738])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( ~ r1_tarski('#skF_3'(A_8,B_9),B_9)
      | r1_tarski(k3_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_859,plain,(
    ! [A_221,A_223] :
      ( r1_tarski(k3_tarski(A_221),A_223)
      | ~ r1_tarski(A_221,k1_zfmisc_1(A_223)) ) ),
    inference(resolution,[status(thm)],[c_820,c_20])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_87,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_76])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [B_80,A_81] :
      ( m1_setfam_1(B_80,A_81)
      | ~ r1_tarski(A_81,k3_tarski(B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_74,plain,(
    ! [B_80] : m1_setfam_1(B_80,k3_tarski(B_80)) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_512,plain,(
    ! [B_174,D_175,C_172,E_176,A_173] :
      ( m1_setfam_1(k6_funct_2(A_173,B_174,C_172,k7_funct_2(A_173,B_174,C_172,D_175)),E_176)
      | ~ m1_setfam_1(D_175,E_176)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(A_173))
      | ~ m1_subset_1(D_175,k1_zfmisc_1(k1_zfmisc_1(A_173)))
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_2(C_172,A_173,B_174)
      | ~ v1_funct_1(C_172)
      | v1_xboole_0(B_174)
      | v1_xboole_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2891,plain,(
    ! [B_394,A_391,E_393,A_392,C_395] :
      ( m1_setfam_1(k6_funct_2(A_391,B_394,C_395,k7_funct_2(A_391,B_394,C_395,A_392)),E_393)
      | ~ m1_setfam_1(A_392,E_393)
      | ~ m1_subset_1(E_393,k1_zfmisc_1(A_391))
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(A_391,B_394)))
      | ~ v1_funct_2(C_395,A_391,B_394)
      | ~ v1_funct_1(C_395)
      | v1_xboole_0(B_394)
      | v1_xboole_0(A_391)
      | ~ r1_tarski(A_392,k1_zfmisc_1(A_391)) ) ),
    inference(resolution,[status(thm)],[c_34,c_512])).

tff(c_2897,plain,(
    ! [B_394,A_19,A_391,E_393,A_392] :
      ( m1_setfam_1(k6_funct_2(A_391,B_394,A_19,k7_funct_2(A_391,B_394,A_19,A_392)),E_393)
      | ~ m1_setfam_1(A_392,E_393)
      | ~ m1_subset_1(E_393,k1_zfmisc_1(A_391))
      | ~ v1_funct_2(A_19,A_391,B_394)
      | ~ v1_funct_1(A_19)
      | v1_xboole_0(B_394)
      | v1_xboole_0(A_391)
      | ~ r1_tarski(A_392,k1_zfmisc_1(A_391))
      | ~ r1_tarski(A_19,k2_zfmisc_1(A_391,B_394)) ) ),
    inference(resolution,[status(thm)],[c_34,c_2891])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,k3_tarski(B_16))
      | ~ m1_setfam_1(B_16,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( m1_subset_1(k7_funct_2(A_25,B_26,C_27,D_28),k1_zfmisc_1(k1_zfmisc_1(B_26)))
      | ~ m1_subset_1(D_28,k1_zfmisc_1(k1_zfmisc_1(A_25)))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ v1_funct_1(C_27)
      | v1_xboole_0(B_26)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_521,plain,(
    ! [B_174,C_172,E_176] :
      ( m1_setfam_1(k6_funct_2('#skF_4',B_174,C_172,k7_funct_2('#skF_4',B_174,C_172,'#skF_7')),E_176)
      | ~ m1_setfam_1('#skF_7',E_176)
      | ~ m1_subset_1(E_176,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_174)))
      | ~ v1_funct_2(C_172,'#skF_4',B_174)
      | ~ v1_funct_1(C_172)
      | v1_xboole_0(B_174)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_512])).

tff(c_625,plain,(
    ! [B_194,C_195,E_196] :
      ( m1_setfam_1(k6_funct_2('#skF_4',B_194,C_195,k7_funct_2('#skF_4',B_194,C_195,'#skF_7')),E_196)
      | ~ m1_setfam_1('#skF_7',E_196)
      | ~ m1_subset_1(E_196,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_194)))
      | ~ v1_funct_2(C_195,'#skF_4',B_194)
      | ~ v1_funct_1(C_195)
      | v1_xboole_0(B_194) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_521])).

tff(c_630,plain,(
    ! [E_196] :
      ( m1_setfam_1(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')),E_196)
      | ~ m1_setfam_1('#skF_7',E_196)
      | ~ m1_subset_1(E_196,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_625])).

tff(c_634,plain,(
    ! [E_196] :
      ( m1_setfam_1(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')),E_196)
      | ~ m1_setfam_1('#skF_7',E_196)
      | ~ m1_subset_1(E_196,k1_zfmisc_1('#skF_4'))
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_630])).

tff(c_635,plain,(
    ! [E_196] :
      ( m1_setfam_1(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')),E_196)
      | ~ m1_setfam_1('#skF_7',E_196)
      | ~ m1_subset_1(E_196,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_634])).

tff(c_36,plain,(
    ! [A_21,B_22,C_23,D_24] :
      ( m1_subset_1(k6_funct_2(A_21,B_22,C_23,D_24),k1_zfmisc_1(k1_zfmisc_1(A_21)))
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k1_zfmisc_1(B_22)))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23)
      | v1_xboole_0(B_22)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3775,plain,(
    ! [E_442,C_441,D_440,B_444,B_443,C_445,A_439] :
      ( m1_setfam_1(k6_funct_2(A_439,B_444,C_445,k7_funct_2(A_439,B_444,C_445,k6_funct_2(A_439,B_443,C_441,D_440))),E_442)
      | ~ m1_setfam_1(k6_funct_2(A_439,B_443,C_441,D_440),E_442)
      | ~ m1_subset_1(E_442,k1_zfmisc_1(A_439))
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_439,B_444)))
      | ~ v1_funct_2(C_445,A_439,B_444)
      | ~ v1_funct_1(C_445)
      | v1_xboole_0(B_444)
      | ~ m1_subset_1(D_440,k1_zfmisc_1(k1_zfmisc_1(B_443)))
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k2_zfmisc_1(A_439,B_443)))
      | ~ v1_funct_2(C_441,A_439,B_443)
      | ~ v1_funct_1(C_441)
      | v1_xboole_0(B_443)
      | v1_xboole_0(A_439) ) ),
    inference(resolution,[status(thm)],[c_36,c_512])).

tff(c_107,plain,(
    ! [A_87,B_88] :
      ( ~ r1_tarski('#skF_3'(A_87,B_88),B_88)
      | r1_tarski(k3_tarski(A_87),B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,(
    ! [A_87,B_16] :
      ( r1_tarski(k3_tarski(A_87),k3_tarski(B_16))
      | ~ m1_setfam_1(B_16,'#skF_3'(A_87,k3_tarski(B_16))) ) ),
    inference(resolution,[status(thm)],[c_26,c_107])).

tff(c_17843,plain,(
    ! [A_995,B_989,A_992,C_994,B_991,D_993,C_990] :
      ( r1_tarski(k3_tarski(A_992),k3_tarski(k6_funct_2(A_995,B_991,C_994,k7_funct_2(A_995,B_991,C_994,k6_funct_2(A_995,B_989,C_990,D_993)))))
      | ~ m1_setfam_1(k6_funct_2(A_995,B_989,C_990,D_993),'#skF_3'(A_992,k3_tarski(k6_funct_2(A_995,B_991,C_994,k7_funct_2(A_995,B_991,C_994,k6_funct_2(A_995,B_989,C_990,D_993))))))
      | ~ m1_subset_1('#skF_3'(A_992,k3_tarski(k6_funct_2(A_995,B_991,C_994,k7_funct_2(A_995,B_991,C_994,k6_funct_2(A_995,B_989,C_990,D_993))))),k1_zfmisc_1(A_995))
      | ~ m1_subset_1(C_994,k1_zfmisc_1(k2_zfmisc_1(A_995,B_991)))
      | ~ v1_funct_2(C_994,A_995,B_991)
      | ~ v1_funct_1(C_994)
      | v1_xboole_0(B_991)
      | ~ m1_subset_1(D_993,k1_zfmisc_1(k1_zfmisc_1(B_989)))
      | ~ m1_subset_1(C_990,k1_zfmisc_1(k2_zfmisc_1(A_995,B_989)))
      | ~ v1_funct_2(C_990,A_995,B_989)
      | ~ v1_funct_1(C_990)
      | v1_xboole_0(B_989)
      | v1_xboole_0(A_995) ) ),
    inference(resolution,[status(thm)],[c_3775,c_111])).

tff(c_17876,plain,(
    ! [A_992,B_991,C_994] :
      ( r1_tarski(k3_tarski(A_992),k3_tarski(k6_funct_2('#skF_4',B_991,C_994,k7_funct_2('#skF_4',B_991,C_994,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))))))
      | ~ m1_subset_1(C_994,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_991)))
      | ~ v1_funct_2(C_994,'#skF_4',B_991)
      | ~ v1_funct_1(C_994)
      | v1_xboole_0(B_991)
      | ~ m1_subset_1(k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | ~ m1_setfam_1('#skF_7','#skF_3'(A_992,k3_tarski(k6_funct_2('#skF_4',B_991,C_994,k7_funct_2('#skF_4',B_991,C_994,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))))))
      | ~ m1_subset_1('#skF_3'(A_992,k3_tarski(k6_funct_2('#skF_4',B_991,C_994,k7_funct_2('#skF_4',B_991,C_994,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))))),k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_635,c_17843])).

tff(c_17897,plain,(
    ! [A_992,B_991,C_994] :
      ( r1_tarski(k3_tarski(A_992),k3_tarski(k6_funct_2('#skF_4',B_991,C_994,k7_funct_2('#skF_4',B_991,C_994,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))))))
      | ~ m1_subset_1(C_994,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_991)))
      | ~ v1_funct_2(C_994,'#skF_4',B_991)
      | ~ v1_funct_1(C_994)
      | v1_xboole_0(B_991)
      | ~ m1_subset_1(k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_5')))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | ~ m1_setfam_1('#skF_7','#skF_3'(A_992,k3_tarski(k6_funct_2('#skF_4',B_991,C_994,k7_funct_2('#skF_4',B_991,C_994,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))))))
      | ~ m1_subset_1('#skF_3'(A_992,k3_tarski(k6_funct_2('#skF_4',B_991,C_994,k7_funct_2('#skF_4',B_991,C_994,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))))),k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_17876])).

tff(c_17898,plain,(
    ! [A_992,B_991,C_994] :
      ( r1_tarski(k3_tarski(A_992),k3_tarski(k6_funct_2('#skF_4',B_991,C_994,k7_funct_2('#skF_4',B_991,C_994,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))))))
      | ~ m1_subset_1(C_994,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_991)))
      | ~ v1_funct_2(C_994,'#skF_4',B_991)
      | ~ v1_funct_1(C_994)
      | v1_xboole_0(B_991)
      | ~ m1_subset_1(k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_5')))
      | ~ m1_setfam_1('#skF_7','#skF_3'(A_992,k3_tarski(k6_funct_2('#skF_4',B_991,C_994,k7_funct_2('#skF_4',B_991,C_994,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))))))
      | ~ m1_subset_1('#skF_3'(A_992,k3_tarski(k6_funct_2('#skF_4',B_991,C_994,k7_funct_2('#skF_4',B_991,C_994,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))))),k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_17897])).

tff(c_19080,plain,(
    ~ m1_subset_1(k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_17898])).

tff(c_19083,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_19080])).

tff(c_19089,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_19083])).

tff(c_19091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_19089])).

tff(c_19093,plain,(
    m1_subset_1(k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_17898])).

tff(c_443,plain,(
    ! [A_144,B_145,C_146,D_147] :
      ( m1_subset_1(k6_funct_2(A_144,B_145,C_146,D_147),k1_zfmisc_1(k1_zfmisc_1(A_144)))
      | ~ m1_subset_1(D_147,k1_zfmisc_1(k1_zfmisc_1(B_145)))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_funct_2(C_146,A_144,B_145)
      | ~ v1_funct_1(C_146)
      | v1_xboole_0(B_145)
      | v1_xboole_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( k5_setfam_1(A_17,B_18) = k3_tarski(B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_450,plain,(
    ! [A_144,B_145,C_146,D_147] :
      ( k5_setfam_1(A_144,k6_funct_2(A_144,B_145,C_146,D_147)) = k3_tarski(k6_funct_2(A_144,B_145,C_146,D_147))
      | ~ m1_subset_1(D_147,k1_zfmisc_1(k1_zfmisc_1(B_145)))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_funct_2(C_146,A_144,B_145)
      | ~ v1_funct_1(C_146)
      | v1_xboole_0(B_145)
      | v1_xboole_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_443,c_30])).

tff(c_19129,plain,(
    ! [A_144,C_146] :
      ( k5_setfam_1(A_144,k6_funct_2(A_144,'#skF_5',C_146,k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))) = k3_tarski(k6_funct_2(A_144,'#skF_5',C_146,k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,'#skF_5')))
      | ~ v1_funct_2(C_146,A_144,'#skF_5')
      | ~ v1_funct_1(C_146)
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_19093,c_450])).

tff(c_19279,plain,(
    ! [A_1035,C_1036] :
      ( k5_setfam_1(A_1035,k6_funct_2(A_1035,'#skF_5',C_1036,k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))) = k3_tarski(k6_funct_2(A_1035,'#skF_5',C_1036,k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))
      | ~ m1_subset_1(C_1036,k1_zfmisc_1(k2_zfmisc_1(A_1035,'#skF_5')))
      | ~ v1_funct_2(C_1036,A_1035,'#skF_5')
      | ~ v1_funct_1(C_1036)
      | v1_xboole_0(A_1035) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_19129])).

tff(c_19284,plain,
    ( k5_setfam_1('#skF_4',k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))) = k3_tarski(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_19279])).

tff(c_19288,plain,
    ( k5_setfam_1('#skF_4',k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))) = k3_tarski(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_19284])).

tff(c_19289,plain,(
    k5_setfam_1('#skF_4',k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))) = k3_tarski(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_19288])).

tff(c_118,plain,(
    ! [A_91,B_92] :
      ( k5_setfam_1(A_91,B_92) = k3_tarski(B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_127,plain,(
    k5_setfam_1('#skF_4','#skF_7') = k3_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_118])).

tff(c_42,plain,(
    ~ r1_tarski(k5_setfam_1('#skF_4','#skF_7'),k5_setfam_1('#skF_4',k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_135,plain,(
    ~ r1_tarski(k3_tarski('#skF_7'),k5_setfam_1('#skF_4',k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_42])).

tff(c_19351,plain,(
    ~ r1_tarski(k3_tarski('#skF_7'),k3_tarski(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19289,c_135])).

tff(c_19385,plain,(
    ~ m1_setfam_1(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')),k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_26,c_19351])).

tff(c_19388,plain,
    ( ~ m1_setfam_1('#skF_7',k3_tarski('#skF_7'))
    | ~ m1_subset_1(k3_tarski('#skF_7'),k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | ~ r1_tarski('#skF_7',k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_2897,c_19385])).

tff(c_19400,plain,
    ( ~ m1_subset_1(k3_tarski('#skF_7'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_88,c_50,c_48,c_74,c_19388])).

tff(c_19401,plain,(
    ~ m1_subset_1(k3_tarski('#skF_7'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_19400])).

tff(c_19415,plain,(
    ~ r1_tarski(k3_tarski('#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_19401])).

tff(c_19436,plain,(
    ~ r1_tarski('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_859,c_19415])).

tff(c_19456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_19436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.57/6.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.61/6.02  
% 13.61/6.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.61/6.02  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > v1_funct_1 > k7_funct_2 > k6_funct_2 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 13.61/6.02  
% 13.61/6.02  %Foreground sorts:
% 13.61/6.02  
% 13.61/6.02  
% 13.61/6.02  %Background operators:
% 13.61/6.02  
% 13.61/6.02  
% 13.61/6.02  %Foreground operators:
% 13.61/6.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.61/6.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.61/6.02  tff(k6_funct_2, type, k6_funct_2: ($i * $i * $i * $i) > $i).
% 13.61/6.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.61/6.02  tff('#skF_7', type, '#skF_7': $i).
% 13.61/6.02  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 13.61/6.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.61/6.02  tff('#skF_5', type, '#skF_5': $i).
% 13.61/6.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.61/6.02  tff('#skF_6', type, '#skF_6': $i).
% 13.61/6.02  tff(k7_funct_2, type, k7_funct_2: ($i * $i * $i * $i) > $i).
% 13.61/6.02  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 13.61/6.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.61/6.02  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 13.61/6.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.61/6.02  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.61/6.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.61/6.02  tff('#skF_4', type, '#skF_4': $i).
% 13.61/6.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.61/6.02  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.61/6.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.61/6.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.61/6.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.61/6.02  
% 13.61/6.04  tff(f_140, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A))) => r1_tarski(k5_setfam_1(A, D), k5_setfam_1(A, k6_funct_2(A, B, C, k7_funct_2(A, B, C, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_funct_2)).
% 13.61/6.04  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.61/6.04  tff(f_45, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 13.61/6.04  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 13.61/6.04  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 13.61/6.04  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.61/6.04  tff(f_56, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 13.61/6.04  tff(f_120, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(A)) => (m1_setfam_1(D, E) => m1_setfam_1(k6_funct_2(A, B, C, k7_funct_2(A, B, C, D)), E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_funct_2)).
% 13.61/6.04  tff(f_96, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A)))) => m1_subset_1(k7_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_funct_2)).
% 13.61/6.04  tff(f_80, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(B)))) => m1_subset_1(k6_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_funct_2)).
% 13.61/6.04  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 13.61/6.04  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 13.61/6.04  tff(c_76, plain, (![A_83, B_84]: (r1_tarski(A_83, B_84) | ~m1_subset_1(A_83, k1_zfmisc_1(B_84)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.61/6.04  tff(c_88, plain, (r1_tarski('#skF_7', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_76])).
% 13.61/6.04  tff(c_34, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.61/6.04  tff(c_22, plain, (![A_8, B_9]: (r2_hidden('#skF_3'(A_8, B_9), A_8) | r1_tarski(k3_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.61/6.04  tff(c_128, plain, (![C_93, A_94, B_95]: (r2_hidden(C_93, A_94) | ~r2_hidden(C_93, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.61/6.04  tff(c_528, plain, (![A_177, B_178, A_179]: (r2_hidden('#skF_3'(A_177, B_178), A_179) | ~m1_subset_1(A_177, k1_zfmisc_1(A_179)) | r1_tarski(k3_tarski(A_177), B_178))), inference(resolution, [status(thm)], [c_22, c_128])).
% 13.61/6.04  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.61/6.04  tff(c_738, plain, (![A_213, B_214, A_215]: (r1_tarski('#skF_3'(A_213, B_214), A_215) | ~m1_subset_1(A_213, k1_zfmisc_1(k1_zfmisc_1(A_215))) | r1_tarski(k3_tarski(A_213), B_214))), inference(resolution, [status(thm)], [c_528, c_8])).
% 13.61/6.04  tff(c_820, plain, (![A_221, B_222, A_223]: (r1_tarski('#skF_3'(A_221, B_222), A_223) | r1_tarski(k3_tarski(A_221), B_222) | ~r1_tarski(A_221, k1_zfmisc_1(A_223)))), inference(resolution, [status(thm)], [c_34, c_738])).
% 13.61/6.04  tff(c_20, plain, (![A_8, B_9]: (~r1_tarski('#skF_3'(A_8, B_9), B_9) | r1_tarski(k3_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.61/6.04  tff(c_859, plain, (![A_221, A_223]: (r1_tarski(k3_tarski(A_221), A_223) | ~r1_tarski(A_221, k1_zfmisc_1(A_223)))), inference(resolution, [status(thm)], [c_820, c_20])).
% 13.61/6.04  tff(c_54, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 13.61/6.04  tff(c_52, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 13.61/6.04  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 13.61/6.04  tff(c_87, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_76])).
% 13.61/6.04  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_140])).
% 13.61/6.04  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 13.61/6.04  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.61/6.04  tff(c_65, plain, (![B_80, A_81]: (m1_setfam_1(B_80, A_81) | ~r1_tarski(A_81, k3_tarski(B_80)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.61/6.04  tff(c_74, plain, (![B_80]: (m1_setfam_1(B_80, k3_tarski(B_80)))), inference(resolution, [status(thm)], [c_6, c_65])).
% 13.61/6.04  tff(c_512, plain, (![B_174, D_175, C_172, E_176, A_173]: (m1_setfam_1(k6_funct_2(A_173, B_174, C_172, k7_funct_2(A_173, B_174, C_172, D_175)), E_176) | ~m1_setfam_1(D_175, E_176) | ~m1_subset_1(E_176, k1_zfmisc_1(A_173)) | ~m1_subset_1(D_175, k1_zfmisc_1(k1_zfmisc_1(A_173))) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_2(C_172, A_173, B_174) | ~v1_funct_1(C_172) | v1_xboole_0(B_174) | v1_xboole_0(A_173))), inference(cnfTransformation, [status(thm)], [f_120])).
% 13.61/6.04  tff(c_2891, plain, (![B_394, A_391, E_393, A_392, C_395]: (m1_setfam_1(k6_funct_2(A_391, B_394, C_395, k7_funct_2(A_391, B_394, C_395, A_392)), E_393) | ~m1_setfam_1(A_392, E_393) | ~m1_subset_1(E_393, k1_zfmisc_1(A_391)) | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1(A_391, B_394))) | ~v1_funct_2(C_395, A_391, B_394) | ~v1_funct_1(C_395) | v1_xboole_0(B_394) | v1_xboole_0(A_391) | ~r1_tarski(A_392, k1_zfmisc_1(A_391)))), inference(resolution, [status(thm)], [c_34, c_512])).
% 13.61/6.04  tff(c_2897, plain, (![B_394, A_19, A_391, E_393, A_392]: (m1_setfam_1(k6_funct_2(A_391, B_394, A_19, k7_funct_2(A_391, B_394, A_19, A_392)), E_393) | ~m1_setfam_1(A_392, E_393) | ~m1_subset_1(E_393, k1_zfmisc_1(A_391)) | ~v1_funct_2(A_19, A_391, B_394) | ~v1_funct_1(A_19) | v1_xboole_0(B_394) | v1_xboole_0(A_391) | ~r1_tarski(A_392, k1_zfmisc_1(A_391)) | ~r1_tarski(A_19, k2_zfmisc_1(A_391, B_394)))), inference(resolution, [status(thm)], [c_34, c_2891])).
% 13.61/6.04  tff(c_26, plain, (![A_15, B_16]: (r1_tarski(A_15, k3_tarski(B_16)) | ~m1_setfam_1(B_16, A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.61/6.04  tff(c_38, plain, (![A_25, B_26, C_27, D_28]: (m1_subset_1(k7_funct_2(A_25, B_26, C_27, D_28), k1_zfmisc_1(k1_zfmisc_1(B_26))) | ~m1_subset_1(D_28, k1_zfmisc_1(k1_zfmisc_1(A_25))) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_2(C_27, A_25, B_26) | ~v1_funct_1(C_27) | v1_xboole_0(B_26) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.61/6.04  tff(c_521, plain, (![B_174, C_172, E_176]: (m1_setfam_1(k6_funct_2('#skF_4', B_174, C_172, k7_funct_2('#skF_4', B_174, C_172, '#skF_7')), E_176) | ~m1_setfam_1('#skF_7', E_176) | ~m1_subset_1(E_176, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_174))) | ~v1_funct_2(C_172, '#skF_4', B_174) | ~v1_funct_1(C_172) | v1_xboole_0(B_174) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_512])).
% 13.61/6.04  tff(c_625, plain, (![B_194, C_195, E_196]: (m1_setfam_1(k6_funct_2('#skF_4', B_194, C_195, k7_funct_2('#skF_4', B_194, C_195, '#skF_7')), E_196) | ~m1_setfam_1('#skF_7', E_196) | ~m1_subset_1(E_196, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_194))) | ~v1_funct_2(C_195, '#skF_4', B_194) | ~v1_funct_1(C_195) | v1_xboole_0(B_194))), inference(negUnitSimplification, [status(thm)], [c_54, c_521])).
% 13.61/6.04  tff(c_630, plain, (![E_196]: (m1_setfam_1(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')), E_196) | ~m1_setfam_1('#skF_7', E_196) | ~m1_subset_1(E_196, k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_625])).
% 13.61/6.04  tff(c_634, plain, (![E_196]: (m1_setfam_1(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')), E_196) | ~m1_setfam_1('#skF_7', E_196) | ~m1_subset_1(E_196, k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_630])).
% 13.61/6.04  tff(c_635, plain, (![E_196]: (m1_setfam_1(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')), E_196) | ~m1_setfam_1('#skF_7', E_196) | ~m1_subset_1(E_196, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_634])).
% 13.61/6.04  tff(c_36, plain, (![A_21, B_22, C_23, D_24]: (m1_subset_1(k6_funct_2(A_21, B_22, C_23, D_24), k1_zfmisc_1(k1_zfmisc_1(A_21))) | ~m1_subset_1(D_24, k1_zfmisc_1(k1_zfmisc_1(B_22))) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23) | v1_xboole_0(B_22) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.61/6.04  tff(c_3775, plain, (![E_442, C_441, D_440, B_444, B_443, C_445, A_439]: (m1_setfam_1(k6_funct_2(A_439, B_444, C_445, k7_funct_2(A_439, B_444, C_445, k6_funct_2(A_439, B_443, C_441, D_440))), E_442) | ~m1_setfam_1(k6_funct_2(A_439, B_443, C_441, D_440), E_442) | ~m1_subset_1(E_442, k1_zfmisc_1(A_439)) | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_439, B_444))) | ~v1_funct_2(C_445, A_439, B_444) | ~v1_funct_1(C_445) | v1_xboole_0(B_444) | ~m1_subset_1(D_440, k1_zfmisc_1(k1_zfmisc_1(B_443))) | ~m1_subset_1(C_441, k1_zfmisc_1(k2_zfmisc_1(A_439, B_443))) | ~v1_funct_2(C_441, A_439, B_443) | ~v1_funct_1(C_441) | v1_xboole_0(B_443) | v1_xboole_0(A_439))), inference(resolution, [status(thm)], [c_36, c_512])).
% 13.61/6.04  tff(c_107, plain, (![A_87, B_88]: (~r1_tarski('#skF_3'(A_87, B_88), B_88) | r1_tarski(k3_tarski(A_87), B_88))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.61/6.04  tff(c_111, plain, (![A_87, B_16]: (r1_tarski(k3_tarski(A_87), k3_tarski(B_16)) | ~m1_setfam_1(B_16, '#skF_3'(A_87, k3_tarski(B_16))))), inference(resolution, [status(thm)], [c_26, c_107])).
% 13.61/6.04  tff(c_17843, plain, (![A_995, B_989, A_992, C_994, B_991, D_993, C_990]: (r1_tarski(k3_tarski(A_992), k3_tarski(k6_funct_2(A_995, B_991, C_994, k7_funct_2(A_995, B_991, C_994, k6_funct_2(A_995, B_989, C_990, D_993))))) | ~m1_setfam_1(k6_funct_2(A_995, B_989, C_990, D_993), '#skF_3'(A_992, k3_tarski(k6_funct_2(A_995, B_991, C_994, k7_funct_2(A_995, B_991, C_994, k6_funct_2(A_995, B_989, C_990, D_993)))))) | ~m1_subset_1('#skF_3'(A_992, k3_tarski(k6_funct_2(A_995, B_991, C_994, k7_funct_2(A_995, B_991, C_994, k6_funct_2(A_995, B_989, C_990, D_993))))), k1_zfmisc_1(A_995)) | ~m1_subset_1(C_994, k1_zfmisc_1(k2_zfmisc_1(A_995, B_991))) | ~v1_funct_2(C_994, A_995, B_991) | ~v1_funct_1(C_994) | v1_xboole_0(B_991) | ~m1_subset_1(D_993, k1_zfmisc_1(k1_zfmisc_1(B_989))) | ~m1_subset_1(C_990, k1_zfmisc_1(k2_zfmisc_1(A_995, B_989))) | ~v1_funct_2(C_990, A_995, B_989) | ~v1_funct_1(C_990) | v1_xboole_0(B_989) | v1_xboole_0(A_995))), inference(resolution, [status(thm)], [c_3775, c_111])).
% 13.61/6.04  tff(c_17876, plain, (![A_992, B_991, C_994]: (r1_tarski(k3_tarski(A_992), k3_tarski(k6_funct_2('#skF_4', B_991, C_994, k7_funct_2('#skF_4', B_991, C_994, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))))) | ~m1_subset_1(C_994, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_991))) | ~v1_funct_2(C_994, '#skF_4', B_991) | ~v1_funct_1(C_994) | v1_xboole_0(B_991) | ~m1_subset_1(k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | ~m1_setfam_1('#skF_7', '#skF_3'(A_992, k3_tarski(k6_funct_2('#skF_4', B_991, C_994, k7_funct_2('#skF_4', B_991, C_994, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))))))) | ~m1_subset_1('#skF_3'(A_992, k3_tarski(k6_funct_2('#skF_4', B_991, C_994, k7_funct_2('#skF_4', B_991, C_994, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))))), k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_635, c_17843])).
% 13.61/6.04  tff(c_17897, plain, (![A_992, B_991, C_994]: (r1_tarski(k3_tarski(A_992), k3_tarski(k6_funct_2('#skF_4', B_991, C_994, k7_funct_2('#skF_4', B_991, C_994, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))))) | ~m1_subset_1(C_994, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_991))) | ~v1_funct_2(C_994, '#skF_4', B_991) | ~v1_funct_1(C_994) | v1_xboole_0(B_991) | ~m1_subset_1(k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | ~m1_setfam_1('#skF_7', '#skF_3'(A_992, k3_tarski(k6_funct_2('#skF_4', B_991, C_994, k7_funct_2('#skF_4', B_991, C_994, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))))))) | ~m1_subset_1('#skF_3'(A_992, k3_tarski(k6_funct_2('#skF_4', B_991, C_994, k7_funct_2('#skF_4', B_991, C_994, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))))), k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_17876])).
% 13.61/6.04  tff(c_17898, plain, (![A_992, B_991, C_994]: (r1_tarski(k3_tarski(A_992), k3_tarski(k6_funct_2('#skF_4', B_991, C_994, k7_funct_2('#skF_4', B_991, C_994, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))))) | ~m1_subset_1(C_994, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_991))) | ~v1_funct_2(C_994, '#skF_4', B_991) | ~v1_funct_1(C_994) | v1_xboole_0(B_991) | ~m1_subset_1(k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) | ~m1_setfam_1('#skF_7', '#skF_3'(A_992, k3_tarski(k6_funct_2('#skF_4', B_991, C_994, k7_funct_2('#skF_4', B_991, C_994, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))))))) | ~m1_subset_1('#skF_3'(A_992, k3_tarski(k6_funct_2('#skF_4', B_991, C_994, k7_funct_2('#skF_4', B_991, C_994, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))))), k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_17897])).
% 13.61/6.04  tff(c_19080, plain, (~m1_subset_1(k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_17898])).
% 13.61/6.04  tff(c_19083, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_19080])).
% 13.61/6.04  tff(c_19089, plain, (v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_19083])).
% 13.61/6.04  tff(c_19091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_19089])).
% 13.61/6.04  tff(c_19093, plain, (m1_subset_1(k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_17898])).
% 13.61/6.04  tff(c_443, plain, (![A_144, B_145, C_146, D_147]: (m1_subset_1(k6_funct_2(A_144, B_145, C_146, D_147), k1_zfmisc_1(k1_zfmisc_1(A_144))) | ~m1_subset_1(D_147, k1_zfmisc_1(k1_zfmisc_1(B_145))) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_funct_2(C_146, A_144, B_145) | ~v1_funct_1(C_146) | v1_xboole_0(B_145) | v1_xboole_0(A_144))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.61/6.04  tff(c_30, plain, (![A_17, B_18]: (k5_setfam_1(A_17, B_18)=k3_tarski(B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.61/6.04  tff(c_450, plain, (![A_144, B_145, C_146, D_147]: (k5_setfam_1(A_144, k6_funct_2(A_144, B_145, C_146, D_147))=k3_tarski(k6_funct_2(A_144, B_145, C_146, D_147)) | ~m1_subset_1(D_147, k1_zfmisc_1(k1_zfmisc_1(B_145))) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_funct_2(C_146, A_144, B_145) | ~v1_funct_1(C_146) | v1_xboole_0(B_145) | v1_xboole_0(A_144))), inference(resolution, [status(thm)], [c_443, c_30])).
% 13.61/6.04  tff(c_19129, plain, (![A_144, C_146]: (k5_setfam_1(A_144, k6_funct_2(A_144, '#skF_5', C_146, k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))=k3_tarski(k6_funct_2(A_144, '#skF_5', C_146, k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, '#skF_5'))) | ~v1_funct_2(C_146, A_144, '#skF_5') | ~v1_funct_1(C_146) | v1_xboole_0('#skF_5') | v1_xboole_0(A_144))), inference(resolution, [status(thm)], [c_19093, c_450])).
% 13.61/6.04  tff(c_19279, plain, (![A_1035, C_1036]: (k5_setfam_1(A_1035, k6_funct_2(A_1035, '#skF_5', C_1036, k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))=k3_tarski(k6_funct_2(A_1035, '#skF_5', C_1036, k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))) | ~m1_subset_1(C_1036, k1_zfmisc_1(k2_zfmisc_1(A_1035, '#skF_5'))) | ~v1_funct_2(C_1036, A_1035, '#skF_5') | ~v1_funct_1(C_1036) | v1_xboole_0(A_1035))), inference(negUnitSimplification, [status(thm)], [c_52, c_19129])).
% 13.61/6.04  tff(c_19284, plain, (k5_setfam_1('#skF_4', k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))=k3_tarski(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_19279])).
% 13.61/6.04  tff(c_19288, plain, (k5_setfam_1('#skF_4', k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))=k3_tarski(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_19284])).
% 13.61/6.04  tff(c_19289, plain, (k5_setfam_1('#skF_4', k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))=k3_tarski(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_54, c_19288])).
% 13.61/6.04  tff(c_118, plain, (![A_91, B_92]: (k5_setfam_1(A_91, B_92)=k3_tarski(B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(k1_zfmisc_1(A_91))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.61/6.04  tff(c_127, plain, (k5_setfam_1('#skF_4', '#skF_7')=k3_tarski('#skF_7')), inference(resolution, [status(thm)], [c_44, c_118])).
% 13.61/6.04  tff(c_42, plain, (~r1_tarski(k5_setfam_1('#skF_4', '#skF_7'), k5_setfam_1('#skF_4', k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 13.61/6.04  tff(c_135, plain, (~r1_tarski(k3_tarski('#skF_7'), k5_setfam_1('#skF_4', k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_42])).
% 13.61/6.04  tff(c_19351, plain, (~r1_tarski(k3_tarski('#skF_7'), k3_tarski(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_19289, c_135])).
% 13.61/6.04  tff(c_19385, plain, (~m1_setfam_1(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')), k3_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_26, c_19351])).
% 13.61/6.04  tff(c_19388, plain, (~m1_setfam_1('#skF_7', k3_tarski('#skF_7')) | ~m1_subset_1(k3_tarski('#skF_7'), k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | ~r1_tarski('#skF_7', k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_2897, c_19385])).
% 13.61/6.04  tff(c_19400, plain, (~m1_subset_1(k3_tarski('#skF_7'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_88, c_50, c_48, c_74, c_19388])).
% 13.61/6.04  tff(c_19401, plain, (~m1_subset_1(k3_tarski('#skF_7'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_19400])).
% 13.61/6.04  tff(c_19415, plain, (~r1_tarski(k3_tarski('#skF_7'), '#skF_4')), inference(resolution, [status(thm)], [c_34, c_19401])).
% 13.61/6.04  tff(c_19436, plain, (~r1_tarski('#skF_7', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_859, c_19415])).
% 13.61/6.04  tff(c_19456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_19436])).
% 13.61/6.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.61/6.04  
% 13.61/6.04  Inference rules
% 13.61/6.04  ----------------------
% 13.61/6.04  #Ref     : 0
% 13.61/6.04  #Sup     : 4394
% 13.61/6.04  #Fact    : 0
% 13.61/6.04  #Define  : 0
% 13.61/6.04  #Split   : 33
% 13.61/6.04  #Chain   : 0
% 13.61/6.04  #Close   : 0
% 13.61/6.04  
% 13.61/6.04  Ordering : KBO
% 13.61/6.04  
% 13.61/6.04  Simplification rules
% 13.61/6.04  ----------------------
% 13.61/6.04  #Subsume      : 269
% 13.61/6.04  #Demod        : 181
% 13.61/6.04  #Tautology    : 134
% 13.61/6.04  #SimpNegUnit  : 39
% 13.61/6.04  #BackRed      : 46
% 13.61/6.04  
% 13.61/6.04  #Partial instantiations: 0
% 13.61/6.04  #Strategies tried      : 1
% 13.61/6.04  
% 13.61/6.04  Timing (in seconds)
% 13.61/6.04  ----------------------
% 13.61/6.05  Preprocessing        : 0.33
% 13.61/6.05  Parsing              : 0.18
% 13.61/6.05  CNF conversion       : 0.03
% 13.61/6.05  Main loop            : 4.92
% 13.61/6.05  Inferencing          : 1.06
% 13.61/6.05  Reduction            : 0.99
% 13.61/6.05  Demodulation         : 0.62
% 13.61/6.05  BG Simplification    : 0.13
% 13.61/6.05  Subsumption          : 2.34
% 13.61/6.05  Abstraction          : 0.18
% 13.61/6.05  MUC search           : 0.00
% 13.61/6.05  Cooper               : 0.00
% 13.61/6.05  Total                : 5.30
% 13.61/6.05  Index Insertion      : 0.00
% 13.61/6.05  Index Deletion       : 0.00
% 13.61/6.05  Index Matching       : 0.00
% 13.61/6.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
