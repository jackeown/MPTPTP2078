%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:46 EST 2020

% Result     : Theorem 29.25s
% Output     : CNFRefutation 29.25s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 922 expanded)
%              Number of leaves         :   57 ( 344 expanded)
%              Depth                    :   19
%              Number of atoms          :  412 (3574 expanded)
%              Number of equality atoms :   88 ( 786 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_11 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_13 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_273,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_154,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_148,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_162,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_158,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_217,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_117,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_193,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_248,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(k2_relset_1(A,B,D),C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_229,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_182,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_132,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_112,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_118,plain,(
    m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_423,plain,(
    ! [C_191,B_192,A_193] :
      ( v5_relat_1(C_191,B_192)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_193,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_442,plain,(
    v5_relat_1('#skF_12','#skF_8') ),
    inference(resolution,[status(thm)],[c_118,c_423])).

tff(c_253,plain,(
    ! [C_157,A_158,B_159] :
      ( v1_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_270,plain,(
    v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_118,c_253])).

tff(c_120,plain,(
    v1_funct_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_116,plain,(
    m1_subset_1('#skF_13','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_126,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_124,plain,(
    v1_funct_2('#skF_11','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_122,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_678,plain,(
    ! [A_240,B_241,C_242] :
      ( k2_relset_1(A_240,B_241,C_242) = k2_relat_1(C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_696,plain,(
    k2_relset_1('#skF_9','#skF_10','#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_122,c_678])).

tff(c_533,plain,(
    ! [A_217,B_218,C_219] :
      ( k1_relset_1(A_217,B_218,C_219) = k1_relat_1(C_219)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218))) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_552,plain,(
    k1_relset_1('#skF_10','#skF_8','#skF_12') = k1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_118,c_533])).

tff(c_114,plain,(
    r1_tarski(k2_relset_1('#skF_9','#skF_10','#skF_11'),k1_relset_1('#skF_10','#skF_8','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_559,plain,(
    r1_tarski(k2_relset_1('#skF_9','#skF_10','#skF_11'),k1_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_114])).

tff(c_699,plain,(
    r1_tarski(k2_relat_1('#skF_11'),k1_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_559])).

tff(c_128,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_2027,plain,(
    ! [E_364,B_361,A_363,F_362,C_359,D_360] :
      ( k1_funct_1(k8_funct_2(B_361,C_359,A_363,D_360,E_364),F_362) = k1_funct_1(E_364,k1_funct_1(D_360,F_362))
      | k1_xboole_0 = B_361
      | ~ r1_tarski(k2_relset_1(B_361,C_359,D_360),k1_relset_1(C_359,A_363,E_364))
      | ~ m1_subset_1(F_362,B_361)
      | ~ m1_subset_1(E_364,k1_zfmisc_1(k2_zfmisc_1(C_359,A_363)))
      | ~ v1_funct_1(E_364)
      | ~ m1_subset_1(D_360,k1_zfmisc_1(k2_zfmisc_1(B_361,C_359)))
      | ~ v1_funct_2(D_360,B_361,C_359)
      | ~ v1_funct_1(D_360)
      | v1_xboole_0(C_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_2041,plain,(
    ! [B_361,D_360,F_362] :
      ( k1_funct_1(k8_funct_2(B_361,'#skF_10','#skF_8',D_360,'#skF_12'),F_362) = k1_funct_1('#skF_12',k1_funct_1(D_360,F_362))
      | k1_xboole_0 = B_361
      | ~ r1_tarski(k2_relset_1(B_361,'#skF_10',D_360),k1_relat_1('#skF_12'))
      | ~ m1_subset_1(F_362,B_361)
      | ~ m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_8')))
      | ~ v1_funct_1('#skF_12')
      | ~ m1_subset_1(D_360,k1_zfmisc_1(k2_zfmisc_1(B_361,'#skF_10')))
      | ~ v1_funct_2(D_360,B_361,'#skF_10')
      | ~ v1_funct_1(D_360)
      | v1_xboole_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_2027])).

tff(c_2060,plain,(
    ! [B_361,D_360,F_362] :
      ( k1_funct_1(k8_funct_2(B_361,'#skF_10','#skF_8',D_360,'#skF_12'),F_362) = k1_funct_1('#skF_12',k1_funct_1(D_360,F_362))
      | k1_xboole_0 = B_361
      | ~ r1_tarski(k2_relset_1(B_361,'#skF_10',D_360),k1_relat_1('#skF_12'))
      | ~ m1_subset_1(F_362,B_361)
      | ~ m1_subset_1(D_360,k1_zfmisc_1(k2_zfmisc_1(B_361,'#skF_10')))
      | ~ v1_funct_2(D_360,B_361,'#skF_10')
      | ~ v1_funct_1(D_360)
      | v1_xboole_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_118,c_2041])).

tff(c_2267,plain,(
    ! [B_374,D_375,F_376] :
      ( k1_funct_1(k8_funct_2(B_374,'#skF_10','#skF_8',D_375,'#skF_12'),F_376) = k1_funct_1('#skF_12',k1_funct_1(D_375,F_376))
      | k1_xboole_0 = B_374
      | ~ r1_tarski(k2_relset_1(B_374,'#skF_10',D_375),k1_relat_1('#skF_12'))
      | ~ m1_subset_1(F_376,B_374)
      | ~ m1_subset_1(D_375,k1_zfmisc_1(k2_zfmisc_1(B_374,'#skF_10')))
      | ~ v1_funct_2(D_375,B_374,'#skF_10')
      | ~ v1_funct_1(D_375) ) ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_2060])).

tff(c_2272,plain,(
    ! [F_376] :
      ( k1_funct_1(k8_funct_2('#skF_9','#skF_10','#skF_8','#skF_11','#skF_12'),F_376) = k1_funct_1('#skF_12',k1_funct_1('#skF_11',F_376))
      | k1_xboole_0 = '#skF_9'
      | ~ r1_tarski(k2_relat_1('#skF_11'),k1_relat_1('#skF_12'))
      | ~ m1_subset_1(F_376,'#skF_9')
      | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10')))
      | ~ v1_funct_2('#skF_11','#skF_9','#skF_10')
      | ~ v1_funct_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_2267])).

tff(c_2277,plain,(
    ! [F_376] :
      ( k1_funct_1(k8_funct_2('#skF_9','#skF_10','#skF_8','#skF_11','#skF_12'),F_376) = k1_funct_1('#skF_12',k1_funct_1('#skF_11',F_376))
      | k1_xboole_0 = '#skF_9'
      | ~ m1_subset_1(F_376,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_124,c_122,c_699,c_2272])).

tff(c_2278,plain,(
    ! [F_376] :
      ( k1_funct_1(k8_funct_2('#skF_9','#skF_10','#skF_8','#skF_11','#skF_12'),F_376) = k1_funct_1('#skF_12',k1_funct_1('#skF_11',F_376))
      | ~ m1_subset_1(F_376,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_2277])).

tff(c_48,plain,(
    ! [A_25,B_28] :
      ( k1_funct_1(A_25,B_28) = k1_xboole_0
      | r2_hidden(B_28,k1_relat_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1126,plain,(
    ! [A_273,B_274,C_275] :
      ( k7_partfun1(A_273,B_274,C_275) = k1_funct_1(B_274,C_275)
      | ~ r2_hidden(C_275,k1_relat_1(B_274))
      | ~ v1_funct_1(B_274)
      | ~ v5_relat_1(B_274,A_273)
      | ~ v1_relat_1(B_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_8657,plain,(
    ! [A_495,A_496,B_497] :
      ( k7_partfun1(A_495,A_496,B_497) = k1_funct_1(A_496,B_497)
      | ~ v5_relat_1(A_496,A_495)
      | k1_funct_1(A_496,B_497) = k1_xboole_0
      | ~ v1_funct_1(A_496)
      | ~ v1_relat_1(A_496) ) ),
    inference(resolution,[status(thm)],[c_48,c_1126])).

tff(c_8669,plain,(
    ! [B_497] :
      ( k7_partfun1('#skF_8','#skF_12',B_497) = k1_funct_1('#skF_12',B_497)
      | k1_funct_1('#skF_12',B_497) = k1_xboole_0
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_442,c_8657])).

tff(c_11511,plain,(
    ! [B_523] :
      ( k7_partfun1('#skF_8','#skF_12',B_523) = k1_funct_1('#skF_12',B_523)
      | k1_funct_1('#skF_12',B_523) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_120,c_8669])).

tff(c_110,plain,(
    k7_partfun1('#skF_8','#skF_12',k1_funct_1('#skF_11','#skF_13')) != k1_funct_1(k8_funct_2('#skF_9','#skF_10','#skF_8','#skF_11','#skF_12'),'#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_11517,plain,
    ( k1_funct_1(k8_funct_2('#skF_9','#skF_10','#skF_8','#skF_11','#skF_12'),'#skF_13') != k1_funct_1('#skF_12',k1_funct_1('#skF_11','#skF_13'))
    | k1_funct_1('#skF_12',k1_funct_1('#skF_11','#skF_13')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11511,c_110])).

tff(c_11884,plain,(
    k1_funct_1(k8_funct_2('#skF_9','#skF_10','#skF_8','#skF_11','#skF_12'),'#skF_13') != k1_funct_1('#skF_12',k1_funct_1('#skF_11','#skF_13')) ),
    inference(splitLeft,[status(thm)],[c_11517])).

tff(c_12705,plain,(
    ~ m1_subset_1('#skF_13','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2278,c_11884])).

tff(c_12709,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_12705])).

tff(c_12710,plain,(
    k1_funct_1('#skF_12',k1_funct_1('#skF_11','#skF_13')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_11517])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_551,plain,(
    k1_relset_1('#skF_9','#skF_10','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_122,c_533])).

tff(c_2043,plain,(
    ! [B_361,D_360,F_362] :
      ( k1_funct_1(k8_funct_2(B_361,'#skF_9','#skF_10',D_360,'#skF_11'),F_362) = k1_funct_1('#skF_11',k1_funct_1(D_360,F_362))
      | k1_xboole_0 = B_361
      | ~ r1_tarski(k2_relset_1(B_361,'#skF_9',D_360),k1_relat_1('#skF_11'))
      | ~ m1_subset_1(F_362,B_361)
      | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10')))
      | ~ v1_funct_1('#skF_11')
      | ~ m1_subset_1(D_360,k1_zfmisc_1(k2_zfmisc_1(B_361,'#skF_9')))
      | ~ v1_funct_2(D_360,B_361,'#skF_9')
      | ~ v1_funct_1(D_360)
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_2027])).

tff(c_2063,plain,(
    ! [B_361,D_360,F_362] :
      ( k1_funct_1(k8_funct_2(B_361,'#skF_9','#skF_10',D_360,'#skF_11'),F_362) = k1_funct_1('#skF_11',k1_funct_1(D_360,F_362))
      | k1_xboole_0 = B_361
      | ~ r1_tarski(k2_relset_1(B_361,'#skF_9',D_360),k1_relat_1('#skF_11'))
      | ~ m1_subset_1(F_362,B_361)
      | ~ m1_subset_1(D_360,k1_zfmisc_1(k2_zfmisc_1(B_361,'#skF_9')))
      | ~ v1_funct_2(D_360,B_361,'#skF_9')
      | ~ v1_funct_1(D_360)
      | v1_xboole_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_122,c_2043])).

tff(c_15815,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2063])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_15832,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_15815,c_8])).

tff(c_15841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_15832])).

tff(c_15843,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_2063])).

tff(c_1742,plain,(
    ! [B_334,D_335,A_336,C_337] :
      ( k1_xboole_0 = B_334
      | v1_funct_2(D_335,A_336,C_337)
      | ~ r1_tarski(k2_relset_1(A_336,B_334,D_335),C_337)
      | ~ m1_subset_1(D_335,k1_zfmisc_1(k2_zfmisc_1(A_336,B_334)))
      | ~ v1_funct_2(D_335,A_336,B_334)
      | ~ v1_funct_1(D_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_1750,plain,(
    ! [C_337] :
      ( k1_xboole_0 = '#skF_10'
      | v1_funct_2('#skF_11','#skF_9',C_337)
      | ~ r1_tarski(k2_relat_1('#skF_11'),C_337)
      | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10')))
      | ~ v1_funct_2('#skF_11','#skF_9','#skF_10')
      | ~ v1_funct_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_1742])).

tff(c_1762,plain,(
    ! [C_337] :
      ( k1_xboole_0 = '#skF_10'
      | v1_funct_2('#skF_11','#skF_9',C_337)
      | ~ r1_tarski(k2_relat_1('#skF_11'),C_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_124,c_122,c_1750])).

tff(c_1855,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1762])).

tff(c_1915,plain,(
    v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1855,c_6])).

tff(c_1918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_1915])).

tff(c_1922,plain,(
    ! [C_342] :
      ( v1_funct_2('#skF_11','#skF_9',C_342)
      | ~ r1_tarski(k2_relat_1('#skF_11'),C_342) ) ),
    inference(splitRight,[status(thm)],[c_1762])).

tff(c_1930,plain,(
    v1_funct_2('#skF_11','#skF_9',k1_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_699,c_1922])).

tff(c_1920,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_1762])).

tff(c_1975,plain,(
    ! [B_348,D_349,A_350,C_351] :
      ( k1_xboole_0 = B_348
      | m1_subset_1(D_349,k1_zfmisc_1(k2_zfmisc_1(A_350,C_351)))
      | ~ r1_tarski(k2_relset_1(A_350,B_348,D_349),C_351)
      | ~ m1_subset_1(D_349,k1_zfmisc_1(k2_zfmisc_1(A_350,B_348)))
      | ~ v1_funct_2(D_349,A_350,B_348)
      | ~ v1_funct_1(D_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_1983,plain,(
    ! [C_351] :
      ( k1_xboole_0 = '#skF_10'
      | m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9',C_351)))
      | ~ r1_tarski(k2_relat_1('#skF_11'),C_351)
      | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10')))
      | ~ v1_funct_2('#skF_11','#skF_9','#skF_10')
      | ~ v1_funct_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_1975])).

tff(c_1995,plain,(
    ! [C_351] :
      ( k1_xboole_0 = '#skF_10'
      | m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9',C_351)))
      | ~ r1_tarski(k2_relat_1('#skF_11'),C_351) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_124,c_122,c_1983])).

tff(c_1996,plain,(
    ! [C_351] :
      ( m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9',C_351)))
      | ~ r1_tarski(k2_relat_1('#skF_11'),C_351) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1920,c_1995])).

tff(c_343,plain,(
    ! [A_176,B_177] :
      ( r2_hidden('#skF_2'(A_176,B_177),B_177)
      | r1_xboole_0(A_176,B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_359,plain,(
    ! [B_179,A_180] :
      ( ~ v1_xboole_0(B_179)
      | r1_xboole_0(A_180,B_179) ) ),
    inference(resolution,[status(thm)],[c_343,c_2])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( ~ r1_xboole_0(B_14,A_13)
      | ~ r1_tarski(B_14,A_13)
      | v1_xboole_0(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_371,plain,(
    ! [A_182,B_183] :
      ( ~ r1_tarski(A_182,B_183)
      | v1_xboole_0(A_182)
      | ~ v1_xboole_0(B_183) ) ),
    inference(resolution,[status(thm)],[c_359,c_22])).

tff(c_384,plain,
    ( v1_xboole_0(k2_relset_1('#skF_9','#skF_10','#skF_11'))
    | ~ v1_xboole_0(k1_relset_1('#skF_10','#skF_8','#skF_12')) ),
    inference(resolution,[status(thm)],[c_114,c_371])).

tff(c_410,plain,(
    ~ v1_xboole_0(k1_relset_1('#skF_10','#skF_8','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_384])).

tff(c_558,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_410])).

tff(c_2064,plain,(
    ! [C_365] :
      ( m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9',C_365)))
      | ~ r1_tarski(k2_relat_1('#skF_11'),C_365) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1920,c_1995])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2122,plain,(
    ! [C_370] :
      ( r1_tarski('#skF_11',k2_zfmisc_1('#skF_9',C_370))
      | ~ r1_tarski(k2_relat_1('#skF_11'),C_370) ) ),
    inference(resolution,[status(thm)],[c_2064,c_34])).

tff(c_2130,plain,(
    r1_tarski('#skF_11',k2_zfmisc_1('#skF_9',k1_relat_1('#skF_12'))) ),
    inference(resolution,[status(thm)],[c_699,c_2122])).

tff(c_36,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3006,plain,(
    ! [A_394,B_395,A_396] :
      ( k2_relset_1(A_394,B_395,A_396) = k2_relat_1(A_396)
      | ~ r1_tarski(A_396,k2_zfmisc_1(A_394,B_395)) ) ),
    inference(resolution,[status(thm)],[c_36,c_678])).

tff(c_3030,plain,(
    k2_relset_1('#skF_9',k1_relat_1('#skF_12'),'#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_2130,c_3006])).

tff(c_94,plain,(
    ! [A_96,F_112,E_110,B_97,C_98,D_106] :
      ( k1_funct_1(k8_funct_2(B_97,C_98,A_96,D_106,E_110),F_112) = k1_funct_1(E_110,k1_funct_1(D_106,F_112))
      | k1_xboole_0 = B_97
      | ~ r1_tarski(k2_relset_1(B_97,C_98,D_106),k1_relset_1(C_98,A_96,E_110))
      | ~ m1_subset_1(F_112,B_97)
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(C_98,A_96)))
      | ~ v1_funct_1(E_110)
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1(B_97,C_98)))
      | ~ v1_funct_2(D_106,B_97,C_98)
      | ~ v1_funct_1(D_106)
      | v1_xboole_0(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_3117,plain,(
    ! [A_96,E_110,F_112] :
      ( k1_funct_1(k8_funct_2('#skF_9',k1_relat_1('#skF_12'),A_96,'#skF_11',E_110),F_112) = k1_funct_1(E_110,k1_funct_1('#skF_11',F_112))
      | k1_xboole_0 = '#skF_9'
      | ~ r1_tarski(k2_relat_1('#skF_11'),k1_relset_1(k1_relat_1('#skF_12'),A_96,E_110))
      | ~ m1_subset_1(F_112,'#skF_9')
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_12'),A_96)))
      | ~ v1_funct_1(E_110)
      | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9',k1_relat_1('#skF_12'))))
      | ~ v1_funct_2('#skF_11','#skF_9',k1_relat_1('#skF_12'))
      | ~ v1_funct_1('#skF_11')
      | v1_xboole_0(k1_relat_1('#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3030,c_94])).

tff(c_3125,plain,(
    ! [A_96,E_110,F_112] :
      ( k1_funct_1(k8_funct_2('#skF_9',k1_relat_1('#skF_12'),A_96,'#skF_11',E_110),F_112) = k1_funct_1(E_110,k1_funct_1('#skF_11',F_112))
      | k1_xboole_0 = '#skF_9'
      | ~ r1_tarski(k2_relat_1('#skF_11'),k1_relset_1(k1_relat_1('#skF_12'),A_96,E_110))
      | ~ m1_subset_1(F_112,'#skF_9')
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_12'),A_96)))
      | ~ v1_funct_1(E_110)
      | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9',k1_relat_1('#skF_12'))))
      | v1_xboole_0(k1_relat_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_1930,c_3117])).

tff(c_3126,plain,(
    ! [A_96,E_110,F_112] :
      ( k1_funct_1(k8_funct_2('#skF_9',k1_relat_1('#skF_12'),A_96,'#skF_11',E_110),F_112) = k1_funct_1(E_110,k1_funct_1('#skF_11',F_112))
      | ~ r1_tarski(k2_relat_1('#skF_11'),k1_relset_1(k1_relat_1('#skF_12'),A_96,E_110))
      | ~ m1_subset_1(F_112,'#skF_9')
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_12'),A_96)))
      | ~ v1_funct_1(E_110)
      | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9',k1_relat_1('#skF_12')))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_558,c_112,c_3125])).

tff(c_3132,plain,(
    ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9',k1_relat_1('#skF_12')))) ),
    inference(splitLeft,[status(thm)],[c_3126])).

tff(c_3168,plain,(
    ~ r1_tarski(k2_relat_1('#skF_11'),k1_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_1996,c_3132])).

tff(c_3175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_3168])).

tff(c_3177,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9',k1_relat_1('#skF_12')))) ),
    inference(splitRight,[status(thm)],[c_3126])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1473,plain,(
    ! [D_307,C_308,B_309,A_310] :
      ( r2_hidden(k1_funct_1(D_307,C_308),B_309)
      | k1_xboole_0 = B_309
      | ~ r2_hidden(C_308,A_310)
      | ~ m1_subset_1(D_307,k1_zfmisc_1(k2_zfmisc_1(A_310,B_309)))
      | ~ v1_funct_2(D_307,A_310,B_309)
      | ~ v1_funct_1(D_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_17251,plain,(
    ! [D_607,A_608,B_609,B_610] :
      ( r2_hidden(k1_funct_1(D_607,A_608),B_609)
      | k1_xboole_0 = B_609
      | ~ m1_subset_1(D_607,k1_zfmisc_1(k2_zfmisc_1(B_610,B_609)))
      | ~ v1_funct_2(D_607,B_610,B_609)
      | ~ v1_funct_1(D_607)
      | v1_xboole_0(B_610)
      | ~ m1_subset_1(A_608,B_610) ) ),
    inference(resolution,[status(thm)],[c_32,c_1473])).

tff(c_17257,plain,(
    ! [A_608] :
      ( r2_hidden(k1_funct_1('#skF_11',A_608),k1_relat_1('#skF_12'))
      | k1_relat_1('#skF_12') = k1_xboole_0
      | ~ v1_funct_2('#skF_11','#skF_9',k1_relat_1('#skF_12'))
      | ~ v1_funct_1('#skF_11')
      | v1_xboole_0('#skF_9')
      | ~ m1_subset_1(A_608,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_3177,c_17251])).

tff(c_17278,plain,(
    ! [A_608] :
      ( r2_hidden(k1_funct_1('#skF_11',A_608),k1_relat_1('#skF_12'))
      | k1_relat_1('#skF_12') = k1_xboole_0
      | v1_xboole_0('#skF_9')
      | ~ m1_subset_1(A_608,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_1930,c_17257])).

tff(c_17279,plain,(
    ! [A_608] :
      ( r2_hidden(k1_funct_1('#skF_11',A_608),k1_relat_1('#skF_12'))
      | k1_relat_1('#skF_12') = k1_xboole_0
      | ~ m1_subset_1(A_608,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_15843,c_17278])).

tff(c_30565,plain,(
    k1_relat_1('#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_17279])).

tff(c_1178,plain,(
    ! [C_278,A_279,B_280] :
      ( ~ v1_xboole_0(C_278)
      | ~ v1_funct_2(C_278,A_279,B_280)
      | ~ v1_funct_1(C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_279,B_280)))
      | v1_xboole_0(B_280)
      | v1_xboole_0(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1185,plain,
    ( ~ v1_xboole_0('#skF_11')
    | ~ v1_funct_2('#skF_11','#skF_9','#skF_10')
    | ~ v1_funct_1('#skF_11')
    | v1_xboole_0('#skF_10')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_122,c_1178])).

tff(c_1198,plain,
    ( ~ v1_xboole_0('#skF_11')
    | v1_xboole_0('#skF_10')
    | v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_124,c_1185])).

tff(c_1199,plain,
    ( ~ v1_xboole_0('#skF_11')
    | v1_xboole_0('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_1198])).

tff(c_1206,plain,(
    ~ v1_xboole_0('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_1199])).

tff(c_363,plain,(
    ! [A_180,B_179] :
      ( ~ r1_tarski(A_180,B_179)
      | v1_xboole_0(A_180)
      | ~ v1_xboole_0(B_179) ) ),
    inference(resolution,[status(thm)],[c_359,c_22])).

tff(c_2251,plain,
    ( v1_xboole_0('#skF_11')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_9',k1_relat_1('#skF_12'))) ),
    inference(resolution,[status(thm)],[c_2130,c_363])).

tff(c_2263,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_9',k1_relat_1('#skF_12'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1206,c_2251])).

tff(c_30576,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_9',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30565,c_2263])).

tff(c_30589,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_26,c_30576])).

tff(c_31385,plain,(
    ! [A_719] :
      ( r2_hidden(k1_funct_1('#skF_11',A_719),k1_relat_1('#skF_12'))
      | ~ m1_subset_1(A_719,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_17279])).

tff(c_50,plain,(
    ! [A_30,D_69] :
      ( r2_hidden(k1_funct_1(A_30,D_69),k2_relat_1(A_30))
      | ~ r2_hidden(D_69,k1_relat_1(A_30))
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_12722,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_12'))
    | ~ r2_hidden(k1_funct_1('#skF_11','#skF_13'),k1_relat_1('#skF_12'))
    | ~ v1_funct_1('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_12710,c_50])).

tff(c_12732,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_12'))
    | ~ r2_hidden(k1_funct_1('#skF_11','#skF_13'),k1_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_120,c_12722])).

tff(c_16524,plain,(
    ~ r2_hidden(k1_funct_1('#skF_11','#skF_13'),k1_relat_1('#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_12732])).

tff(c_31392,plain,(
    ~ m1_subset_1('#skF_13','#skF_9') ),
    inference(resolution,[status(thm)],[c_31385,c_16524])).

tff(c_31435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_31392])).

tff(c_31437,plain,(
    r2_hidden(k1_funct_1('#skF_11','#skF_13'),k1_relat_1('#skF_12')) ),
    inference(splitRight,[status(thm)],[c_12732])).

tff(c_92,plain,(
    ! [A_92,B_93,C_95] :
      ( k7_partfun1(A_92,B_93,C_95) = k1_funct_1(B_93,C_95)
      | ~ r2_hidden(C_95,k1_relat_1(B_93))
      | ~ v1_funct_1(B_93)
      | ~ v5_relat_1(B_93,A_92)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_31607,plain,(
    ! [A_92] :
      ( k7_partfun1(A_92,'#skF_12',k1_funct_1('#skF_11','#skF_13')) = k1_funct_1('#skF_12',k1_funct_1('#skF_11','#skF_13'))
      | ~ v1_funct_1('#skF_12')
      | ~ v5_relat_1('#skF_12',A_92)
      | ~ v1_relat_1('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_31437,c_92])).

tff(c_111682,plain,(
    ! [A_1171] :
      ( k7_partfun1(A_1171,'#skF_12',k1_funct_1('#skF_11','#skF_13')) = k1_xboole_0
      | ~ v5_relat_1('#skF_12',A_1171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_120,c_12710,c_31607])).

tff(c_12711,plain,(
    k1_funct_1(k8_funct_2('#skF_9','#skF_10','#skF_8','#skF_11','#skF_12'),'#skF_13') = k1_funct_1('#skF_12',k1_funct_1('#skF_11','#skF_13')) ),
    inference(splitRight,[status(thm)],[c_11517])).

tff(c_12932,plain,(
    k1_funct_1(k8_funct_2('#skF_9','#skF_10','#skF_8','#skF_11','#skF_12'),'#skF_13') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12710,c_12711])).

tff(c_12933,plain,(
    k7_partfun1('#skF_8','#skF_12',k1_funct_1('#skF_11','#skF_13')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12932,c_110])).

tff(c_111688,plain,(
    ~ v5_relat_1('#skF_12','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_111682,c_12933])).

tff(c_111705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_111688])).

tff(c_111706,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1199])).

tff(c_111713,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_111706,c_8])).

tff(c_111718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_111713])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:45:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.25/20.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.25/20.34  
% 29.25/20.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.25/20.34  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_11 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_13 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_12 > #skF_4
% 29.25/20.34  
% 29.25/20.34  %Foreground sorts:
% 29.25/20.34  
% 29.25/20.34  
% 29.25/20.34  %Background operators:
% 29.25/20.34  
% 29.25/20.34  
% 29.25/20.34  %Foreground operators:
% 29.25/20.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 29.25/20.34  tff('#skF_7', type, '#skF_7': $i > $i).
% 29.25/20.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 29.25/20.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.25/20.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 29.25/20.34  tff('#skF_11', type, '#skF_11': $i).
% 29.25/20.34  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 29.25/20.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 29.25/20.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 29.25/20.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 29.25/20.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 29.25/20.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.25/20.34  tff('#skF_10', type, '#skF_10': $i).
% 29.25/20.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 29.25/20.34  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 29.25/20.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 29.25/20.34  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 29.25/20.34  tff('#skF_13', type, '#skF_13': $i).
% 29.25/20.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 29.25/20.34  tff('#skF_9', type, '#skF_9': $i).
% 29.25/20.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 29.25/20.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 29.25/20.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 29.25/20.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 29.25/20.34  tff('#skF_8', type, '#skF_8': $i).
% 29.25/20.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.25/20.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 29.25/20.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 29.25/20.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.25/20.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 29.25/20.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 29.25/20.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 29.25/20.34  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 29.25/20.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 29.25/20.34  tff('#skF_12', type, '#skF_12': $i).
% 29.25/20.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 29.25/20.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 29.25/20.34  
% 29.25/20.37  tff(f_273, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 29.25/20.37  tff(f_154, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 29.25/20.37  tff(f_148, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 29.25/20.37  tff(f_162, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 29.25/20.37  tff(f_158, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 29.25/20.37  tff(f_217, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 29.25/20.37  tff(f_117, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 29.25/20.37  tff(f_193, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 29.25/20.37  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 29.25/20.37  tff(f_74, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 29.25/20.37  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 29.25/20.37  tff(f_248, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 29.25/20.37  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 29.25/20.37  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 29.25/20.37  tff(f_68, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 29.25/20.37  tff(f_87, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 29.25/20.37  tff(f_83, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 29.25/20.37  tff(f_229, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 29.25/20.37  tff(f_182, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 29.25/20.37  tff(f_132, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 29.25/20.37  tff(c_112, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_273])).
% 29.25/20.37  tff(c_118, plain, (m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_273])).
% 29.25/20.37  tff(c_423, plain, (![C_191, B_192, A_193]: (v5_relat_1(C_191, B_192) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_193, B_192))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 29.25/20.37  tff(c_442, plain, (v5_relat_1('#skF_12', '#skF_8')), inference(resolution, [status(thm)], [c_118, c_423])).
% 29.25/20.37  tff(c_253, plain, (![C_157, A_158, B_159]: (v1_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 29.25/20.37  tff(c_270, plain, (v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_118, c_253])).
% 29.25/20.37  tff(c_120, plain, (v1_funct_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_273])).
% 29.25/20.37  tff(c_116, plain, (m1_subset_1('#skF_13', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_273])).
% 29.25/20.37  tff(c_126, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_273])).
% 29.25/20.37  tff(c_124, plain, (v1_funct_2('#skF_11', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_273])).
% 29.25/20.37  tff(c_122, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_273])).
% 29.25/20.37  tff(c_678, plain, (![A_240, B_241, C_242]: (k2_relset_1(A_240, B_241, C_242)=k2_relat_1(C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 29.25/20.37  tff(c_696, plain, (k2_relset_1('#skF_9', '#skF_10', '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_122, c_678])).
% 29.25/20.37  tff(c_533, plain, (![A_217, B_218, C_219]: (k1_relset_1(A_217, B_218, C_219)=k1_relat_1(C_219) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 29.25/20.37  tff(c_552, plain, (k1_relset_1('#skF_10', '#skF_8', '#skF_12')=k1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_118, c_533])).
% 29.25/20.37  tff(c_114, plain, (r1_tarski(k2_relset_1('#skF_9', '#skF_10', '#skF_11'), k1_relset_1('#skF_10', '#skF_8', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_273])).
% 29.25/20.37  tff(c_559, plain, (r1_tarski(k2_relset_1('#skF_9', '#skF_10', '#skF_11'), k1_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_552, c_114])).
% 29.25/20.37  tff(c_699, plain, (r1_tarski(k2_relat_1('#skF_11'), k1_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_696, c_559])).
% 29.25/20.37  tff(c_128, plain, (~v1_xboole_0('#skF_10')), inference(cnfTransformation, [status(thm)], [f_273])).
% 29.25/20.37  tff(c_2027, plain, (![E_364, B_361, A_363, F_362, C_359, D_360]: (k1_funct_1(k8_funct_2(B_361, C_359, A_363, D_360, E_364), F_362)=k1_funct_1(E_364, k1_funct_1(D_360, F_362)) | k1_xboole_0=B_361 | ~r1_tarski(k2_relset_1(B_361, C_359, D_360), k1_relset_1(C_359, A_363, E_364)) | ~m1_subset_1(F_362, B_361) | ~m1_subset_1(E_364, k1_zfmisc_1(k2_zfmisc_1(C_359, A_363))) | ~v1_funct_1(E_364) | ~m1_subset_1(D_360, k1_zfmisc_1(k2_zfmisc_1(B_361, C_359))) | ~v1_funct_2(D_360, B_361, C_359) | ~v1_funct_1(D_360) | v1_xboole_0(C_359))), inference(cnfTransformation, [status(thm)], [f_217])).
% 29.25/20.37  tff(c_2041, plain, (![B_361, D_360, F_362]: (k1_funct_1(k8_funct_2(B_361, '#skF_10', '#skF_8', D_360, '#skF_12'), F_362)=k1_funct_1('#skF_12', k1_funct_1(D_360, F_362)) | k1_xboole_0=B_361 | ~r1_tarski(k2_relset_1(B_361, '#skF_10', D_360), k1_relat_1('#skF_12')) | ~m1_subset_1(F_362, B_361) | ~m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_8'))) | ~v1_funct_1('#skF_12') | ~m1_subset_1(D_360, k1_zfmisc_1(k2_zfmisc_1(B_361, '#skF_10'))) | ~v1_funct_2(D_360, B_361, '#skF_10') | ~v1_funct_1(D_360) | v1_xboole_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_552, c_2027])).
% 29.25/20.37  tff(c_2060, plain, (![B_361, D_360, F_362]: (k1_funct_1(k8_funct_2(B_361, '#skF_10', '#skF_8', D_360, '#skF_12'), F_362)=k1_funct_1('#skF_12', k1_funct_1(D_360, F_362)) | k1_xboole_0=B_361 | ~r1_tarski(k2_relset_1(B_361, '#skF_10', D_360), k1_relat_1('#skF_12')) | ~m1_subset_1(F_362, B_361) | ~m1_subset_1(D_360, k1_zfmisc_1(k2_zfmisc_1(B_361, '#skF_10'))) | ~v1_funct_2(D_360, B_361, '#skF_10') | ~v1_funct_1(D_360) | v1_xboole_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_118, c_2041])).
% 29.25/20.37  tff(c_2267, plain, (![B_374, D_375, F_376]: (k1_funct_1(k8_funct_2(B_374, '#skF_10', '#skF_8', D_375, '#skF_12'), F_376)=k1_funct_1('#skF_12', k1_funct_1(D_375, F_376)) | k1_xboole_0=B_374 | ~r1_tarski(k2_relset_1(B_374, '#skF_10', D_375), k1_relat_1('#skF_12')) | ~m1_subset_1(F_376, B_374) | ~m1_subset_1(D_375, k1_zfmisc_1(k2_zfmisc_1(B_374, '#skF_10'))) | ~v1_funct_2(D_375, B_374, '#skF_10') | ~v1_funct_1(D_375))), inference(negUnitSimplification, [status(thm)], [c_128, c_2060])).
% 29.25/20.37  tff(c_2272, plain, (![F_376]: (k1_funct_1(k8_funct_2('#skF_9', '#skF_10', '#skF_8', '#skF_11', '#skF_12'), F_376)=k1_funct_1('#skF_12', k1_funct_1('#skF_11', F_376)) | k1_xboole_0='#skF_9' | ~r1_tarski(k2_relat_1('#skF_11'), k1_relat_1('#skF_12')) | ~m1_subset_1(F_376, '#skF_9') | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10'))) | ~v1_funct_2('#skF_11', '#skF_9', '#skF_10') | ~v1_funct_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_696, c_2267])).
% 29.25/20.37  tff(c_2277, plain, (![F_376]: (k1_funct_1(k8_funct_2('#skF_9', '#skF_10', '#skF_8', '#skF_11', '#skF_12'), F_376)=k1_funct_1('#skF_12', k1_funct_1('#skF_11', F_376)) | k1_xboole_0='#skF_9' | ~m1_subset_1(F_376, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_124, c_122, c_699, c_2272])).
% 29.25/20.37  tff(c_2278, plain, (![F_376]: (k1_funct_1(k8_funct_2('#skF_9', '#skF_10', '#skF_8', '#skF_11', '#skF_12'), F_376)=k1_funct_1('#skF_12', k1_funct_1('#skF_11', F_376)) | ~m1_subset_1(F_376, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_112, c_2277])).
% 29.25/20.37  tff(c_48, plain, (![A_25, B_28]: (k1_funct_1(A_25, B_28)=k1_xboole_0 | r2_hidden(B_28, k1_relat_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_117])).
% 29.25/20.37  tff(c_1126, plain, (![A_273, B_274, C_275]: (k7_partfun1(A_273, B_274, C_275)=k1_funct_1(B_274, C_275) | ~r2_hidden(C_275, k1_relat_1(B_274)) | ~v1_funct_1(B_274) | ~v5_relat_1(B_274, A_273) | ~v1_relat_1(B_274))), inference(cnfTransformation, [status(thm)], [f_193])).
% 29.25/20.37  tff(c_8657, plain, (![A_495, A_496, B_497]: (k7_partfun1(A_495, A_496, B_497)=k1_funct_1(A_496, B_497) | ~v5_relat_1(A_496, A_495) | k1_funct_1(A_496, B_497)=k1_xboole_0 | ~v1_funct_1(A_496) | ~v1_relat_1(A_496))), inference(resolution, [status(thm)], [c_48, c_1126])).
% 29.25/20.37  tff(c_8669, plain, (![B_497]: (k7_partfun1('#skF_8', '#skF_12', B_497)=k1_funct_1('#skF_12', B_497) | k1_funct_1('#skF_12', B_497)=k1_xboole_0 | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_442, c_8657])).
% 29.25/20.37  tff(c_11511, plain, (![B_523]: (k7_partfun1('#skF_8', '#skF_12', B_523)=k1_funct_1('#skF_12', B_523) | k1_funct_1('#skF_12', B_523)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_270, c_120, c_8669])).
% 29.25/20.37  tff(c_110, plain, (k7_partfun1('#skF_8', '#skF_12', k1_funct_1('#skF_11', '#skF_13'))!=k1_funct_1(k8_funct_2('#skF_9', '#skF_10', '#skF_8', '#skF_11', '#skF_12'), '#skF_13')), inference(cnfTransformation, [status(thm)], [f_273])).
% 29.25/20.37  tff(c_11517, plain, (k1_funct_1(k8_funct_2('#skF_9', '#skF_10', '#skF_8', '#skF_11', '#skF_12'), '#skF_13')!=k1_funct_1('#skF_12', k1_funct_1('#skF_11', '#skF_13')) | k1_funct_1('#skF_12', k1_funct_1('#skF_11', '#skF_13'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11511, c_110])).
% 29.25/20.37  tff(c_11884, plain, (k1_funct_1(k8_funct_2('#skF_9', '#skF_10', '#skF_8', '#skF_11', '#skF_12'), '#skF_13')!=k1_funct_1('#skF_12', k1_funct_1('#skF_11', '#skF_13'))), inference(splitLeft, [status(thm)], [c_11517])).
% 29.25/20.37  tff(c_12705, plain, (~m1_subset_1('#skF_13', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2278, c_11884])).
% 29.25/20.37  tff(c_12709, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_12705])).
% 29.25/20.37  tff(c_12710, plain, (k1_funct_1('#skF_12', k1_funct_1('#skF_11', '#skF_13'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_11517])).
% 29.25/20.37  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 29.25/20.37  tff(c_26, plain, (![A_15]: (k2_zfmisc_1(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 29.25/20.37  tff(c_551, plain, (k1_relset_1('#skF_9', '#skF_10', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_122, c_533])).
% 29.25/20.37  tff(c_2043, plain, (![B_361, D_360, F_362]: (k1_funct_1(k8_funct_2(B_361, '#skF_9', '#skF_10', D_360, '#skF_11'), F_362)=k1_funct_1('#skF_11', k1_funct_1(D_360, F_362)) | k1_xboole_0=B_361 | ~r1_tarski(k2_relset_1(B_361, '#skF_9', D_360), k1_relat_1('#skF_11')) | ~m1_subset_1(F_362, B_361) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10'))) | ~v1_funct_1('#skF_11') | ~m1_subset_1(D_360, k1_zfmisc_1(k2_zfmisc_1(B_361, '#skF_9'))) | ~v1_funct_2(D_360, B_361, '#skF_9') | ~v1_funct_1(D_360) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_551, c_2027])).
% 29.25/20.37  tff(c_2063, plain, (![B_361, D_360, F_362]: (k1_funct_1(k8_funct_2(B_361, '#skF_9', '#skF_10', D_360, '#skF_11'), F_362)=k1_funct_1('#skF_11', k1_funct_1(D_360, F_362)) | k1_xboole_0=B_361 | ~r1_tarski(k2_relset_1(B_361, '#skF_9', D_360), k1_relat_1('#skF_11')) | ~m1_subset_1(F_362, B_361) | ~m1_subset_1(D_360, k1_zfmisc_1(k2_zfmisc_1(B_361, '#skF_9'))) | ~v1_funct_2(D_360, B_361, '#skF_9') | ~v1_funct_1(D_360) | v1_xboole_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_122, c_2043])).
% 29.25/20.37  tff(c_15815, plain, (v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_2063])).
% 29.25/20.37  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 29.25/20.37  tff(c_15832, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_15815, c_8])).
% 29.25/20.37  tff(c_15841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_15832])).
% 29.25/20.37  tff(c_15843, plain, (~v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_2063])).
% 29.25/20.37  tff(c_1742, plain, (![B_334, D_335, A_336, C_337]: (k1_xboole_0=B_334 | v1_funct_2(D_335, A_336, C_337) | ~r1_tarski(k2_relset_1(A_336, B_334, D_335), C_337) | ~m1_subset_1(D_335, k1_zfmisc_1(k2_zfmisc_1(A_336, B_334))) | ~v1_funct_2(D_335, A_336, B_334) | ~v1_funct_1(D_335))), inference(cnfTransformation, [status(thm)], [f_248])).
% 29.25/20.37  tff(c_1750, plain, (![C_337]: (k1_xboole_0='#skF_10' | v1_funct_2('#skF_11', '#skF_9', C_337) | ~r1_tarski(k2_relat_1('#skF_11'), C_337) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10'))) | ~v1_funct_2('#skF_11', '#skF_9', '#skF_10') | ~v1_funct_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_696, c_1742])).
% 29.25/20.37  tff(c_1762, plain, (![C_337]: (k1_xboole_0='#skF_10' | v1_funct_2('#skF_11', '#skF_9', C_337) | ~r1_tarski(k2_relat_1('#skF_11'), C_337))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_124, c_122, c_1750])).
% 29.25/20.37  tff(c_1855, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_1762])).
% 29.25/20.37  tff(c_1915, plain, (v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1855, c_6])).
% 29.25/20.37  tff(c_1918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_1915])).
% 29.25/20.37  tff(c_1922, plain, (![C_342]: (v1_funct_2('#skF_11', '#skF_9', C_342) | ~r1_tarski(k2_relat_1('#skF_11'), C_342))), inference(splitRight, [status(thm)], [c_1762])).
% 29.25/20.37  tff(c_1930, plain, (v1_funct_2('#skF_11', '#skF_9', k1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_699, c_1922])).
% 29.25/20.37  tff(c_1920, plain, (k1_xboole_0!='#skF_10'), inference(splitRight, [status(thm)], [c_1762])).
% 29.25/20.37  tff(c_1975, plain, (![B_348, D_349, A_350, C_351]: (k1_xboole_0=B_348 | m1_subset_1(D_349, k1_zfmisc_1(k2_zfmisc_1(A_350, C_351))) | ~r1_tarski(k2_relset_1(A_350, B_348, D_349), C_351) | ~m1_subset_1(D_349, k1_zfmisc_1(k2_zfmisc_1(A_350, B_348))) | ~v1_funct_2(D_349, A_350, B_348) | ~v1_funct_1(D_349))), inference(cnfTransformation, [status(thm)], [f_248])).
% 29.25/20.37  tff(c_1983, plain, (![C_351]: (k1_xboole_0='#skF_10' | m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', C_351))) | ~r1_tarski(k2_relat_1('#skF_11'), C_351) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10'))) | ~v1_funct_2('#skF_11', '#skF_9', '#skF_10') | ~v1_funct_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_696, c_1975])).
% 29.25/20.37  tff(c_1995, plain, (![C_351]: (k1_xboole_0='#skF_10' | m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', C_351))) | ~r1_tarski(k2_relat_1('#skF_11'), C_351))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_124, c_122, c_1983])).
% 29.25/20.37  tff(c_1996, plain, (![C_351]: (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', C_351))) | ~r1_tarski(k2_relat_1('#skF_11'), C_351))), inference(negUnitSimplification, [status(thm)], [c_1920, c_1995])).
% 29.25/20.37  tff(c_343, plain, (![A_176, B_177]: (r2_hidden('#skF_2'(A_176, B_177), B_177) | r1_xboole_0(A_176, B_177))), inference(cnfTransformation, [status(thm)], [f_54])).
% 29.25/20.37  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.25/20.37  tff(c_359, plain, (![B_179, A_180]: (~v1_xboole_0(B_179) | r1_xboole_0(A_180, B_179))), inference(resolution, [status(thm)], [c_343, c_2])).
% 29.25/20.37  tff(c_22, plain, (![B_14, A_13]: (~r1_xboole_0(B_14, A_13) | ~r1_tarski(B_14, A_13) | v1_xboole_0(B_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 29.25/20.37  tff(c_371, plain, (![A_182, B_183]: (~r1_tarski(A_182, B_183) | v1_xboole_0(A_182) | ~v1_xboole_0(B_183))), inference(resolution, [status(thm)], [c_359, c_22])).
% 29.25/20.37  tff(c_384, plain, (v1_xboole_0(k2_relset_1('#skF_9', '#skF_10', '#skF_11')) | ~v1_xboole_0(k1_relset_1('#skF_10', '#skF_8', '#skF_12'))), inference(resolution, [status(thm)], [c_114, c_371])).
% 29.25/20.37  tff(c_410, plain, (~v1_xboole_0(k1_relset_1('#skF_10', '#skF_8', '#skF_12'))), inference(splitLeft, [status(thm)], [c_384])).
% 29.25/20.37  tff(c_558, plain, (~v1_xboole_0(k1_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_552, c_410])).
% 29.25/20.37  tff(c_2064, plain, (![C_365]: (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', C_365))) | ~r1_tarski(k2_relat_1('#skF_11'), C_365))), inference(negUnitSimplification, [status(thm)], [c_1920, c_1995])).
% 29.25/20.37  tff(c_34, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 29.25/20.37  tff(c_2122, plain, (![C_370]: (r1_tarski('#skF_11', k2_zfmisc_1('#skF_9', C_370)) | ~r1_tarski(k2_relat_1('#skF_11'), C_370))), inference(resolution, [status(thm)], [c_2064, c_34])).
% 29.25/20.37  tff(c_2130, plain, (r1_tarski('#skF_11', k2_zfmisc_1('#skF_9', k1_relat_1('#skF_12')))), inference(resolution, [status(thm)], [c_699, c_2122])).
% 29.25/20.37  tff(c_36, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_87])).
% 29.25/20.37  tff(c_3006, plain, (![A_394, B_395, A_396]: (k2_relset_1(A_394, B_395, A_396)=k2_relat_1(A_396) | ~r1_tarski(A_396, k2_zfmisc_1(A_394, B_395)))), inference(resolution, [status(thm)], [c_36, c_678])).
% 29.25/20.37  tff(c_3030, plain, (k2_relset_1('#skF_9', k1_relat_1('#skF_12'), '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_2130, c_3006])).
% 29.25/20.37  tff(c_94, plain, (![A_96, F_112, E_110, B_97, C_98, D_106]: (k1_funct_1(k8_funct_2(B_97, C_98, A_96, D_106, E_110), F_112)=k1_funct_1(E_110, k1_funct_1(D_106, F_112)) | k1_xboole_0=B_97 | ~r1_tarski(k2_relset_1(B_97, C_98, D_106), k1_relset_1(C_98, A_96, E_110)) | ~m1_subset_1(F_112, B_97) | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(C_98, A_96))) | ~v1_funct_1(E_110) | ~m1_subset_1(D_106, k1_zfmisc_1(k2_zfmisc_1(B_97, C_98))) | ~v1_funct_2(D_106, B_97, C_98) | ~v1_funct_1(D_106) | v1_xboole_0(C_98))), inference(cnfTransformation, [status(thm)], [f_217])).
% 29.25/20.37  tff(c_3117, plain, (![A_96, E_110, F_112]: (k1_funct_1(k8_funct_2('#skF_9', k1_relat_1('#skF_12'), A_96, '#skF_11', E_110), F_112)=k1_funct_1(E_110, k1_funct_1('#skF_11', F_112)) | k1_xboole_0='#skF_9' | ~r1_tarski(k2_relat_1('#skF_11'), k1_relset_1(k1_relat_1('#skF_12'), A_96, E_110)) | ~m1_subset_1(F_112, '#skF_9') | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_12'), A_96))) | ~v1_funct_1(E_110) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', k1_relat_1('#skF_12')))) | ~v1_funct_2('#skF_11', '#skF_9', k1_relat_1('#skF_12')) | ~v1_funct_1('#skF_11') | v1_xboole_0(k1_relat_1('#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_3030, c_94])).
% 29.25/20.37  tff(c_3125, plain, (![A_96, E_110, F_112]: (k1_funct_1(k8_funct_2('#skF_9', k1_relat_1('#skF_12'), A_96, '#skF_11', E_110), F_112)=k1_funct_1(E_110, k1_funct_1('#skF_11', F_112)) | k1_xboole_0='#skF_9' | ~r1_tarski(k2_relat_1('#skF_11'), k1_relset_1(k1_relat_1('#skF_12'), A_96, E_110)) | ~m1_subset_1(F_112, '#skF_9') | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_12'), A_96))) | ~v1_funct_1(E_110) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', k1_relat_1('#skF_12')))) | v1_xboole_0(k1_relat_1('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_1930, c_3117])).
% 29.25/20.37  tff(c_3126, plain, (![A_96, E_110, F_112]: (k1_funct_1(k8_funct_2('#skF_9', k1_relat_1('#skF_12'), A_96, '#skF_11', E_110), F_112)=k1_funct_1(E_110, k1_funct_1('#skF_11', F_112)) | ~r1_tarski(k2_relat_1('#skF_11'), k1_relset_1(k1_relat_1('#skF_12'), A_96, E_110)) | ~m1_subset_1(F_112, '#skF_9') | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_12'), A_96))) | ~v1_funct_1(E_110) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', k1_relat_1('#skF_12')))))), inference(negUnitSimplification, [status(thm)], [c_558, c_112, c_3125])).
% 29.25/20.37  tff(c_3132, plain, (~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', k1_relat_1('#skF_12'))))), inference(splitLeft, [status(thm)], [c_3126])).
% 29.25/20.37  tff(c_3168, plain, (~r1_tarski(k2_relat_1('#skF_11'), k1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_1996, c_3132])).
% 29.25/20.37  tff(c_3175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_699, c_3168])).
% 29.25/20.37  tff(c_3177, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', k1_relat_1('#skF_12'))))), inference(splitRight, [status(thm)], [c_3126])).
% 29.25/20.37  tff(c_32, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 29.25/20.37  tff(c_1473, plain, (![D_307, C_308, B_309, A_310]: (r2_hidden(k1_funct_1(D_307, C_308), B_309) | k1_xboole_0=B_309 | ~r2_hidden(C_308, A_310) | ~m1_subset_1(D_307, k1_zfmisc_1(k2_zfmisc_1(A_310, B_309))) | ~v1_funct_2(D_307, A_310, B_309) | ~v1_funct_1(D_307))), inference(cnfTransformation, [status(thm)], [f_229])).
% 29.25/20.37  tff(c_17251, plain, (![D_607, A_608, B_609, B_610]: (r2_hidden(k1_funct_1(D_607, A_608), B_609) | k1_xboole_0=B_609 | ~m1_subset_1(D_607, k1_zfmisc_1(k2_zfmisc_1(B_610, B_609))) | ~v1_funct_2(D_607, B_610, B_609) | ~v1_funct_1(D_607) | v1_xboole_0(B_610) | ~m1_subset_1(A_608, B_610))), inference(resolution, [status(thm)], [c_32, c_1473])).
% 29.25/20.37  tff(c_17257, plain, (![A_608]: (r2_hidden(k1_funct_1('#skF_11', A_608), k1_relat_1('#skF_12')) | k1_relat_1('#skF_12')=k1_xboole_0 | ~v1_funct_2('#skF_11', '#skF_9', k1_relat_1('#skF_12')) | ~v1_funct_1('#skF_11') | v1_xboole_0('#skF_9') | ~m1_subset_1(A_608, '#skF_9'))), inference(resolution, [status(thm)], [c_3177, c_17251])).
% 29.25/20.37  tff(c_17278, plain, (![A_608]: (r2_hidden(k1_funct_1('#skF_11', A_608), k1_relat_1('#skF_12')) | k1_relat_1('#skF_12')=k1_xboole_0 | v1_xboole_0('#skF_9') | ~m1_subset_1(A_608, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_1930, c_17257])).
% 29.25/20.37  tff(c_17279, plain, (![A_608]: (r2_hidden(k1_funct_1('#skF_11', A_608), k1_relat_1('#skF_12')) | k1_relat_1('#skF_12')=k1_xboole_0 | ~m1_subset_1(A_608, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_15843, c_17278])).
% 29.25/20.37  tff(c_30565, plain, (k1_relat_1('#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_17279])).
% 29.25/20.37  tff(c_1178, plain, (![C_278, A_279, B_280]: (~v1_xboole_0(C_278) | ~v1_funct_2(C_278, A_279, B_280) | ~v1_funct_1(C_278) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_279, B_280))) | v1_xboole_0(B_280) | v1_xboole_0(A_279))), inference(cnfTransformation, [status(thm)], [f_182])).
% 29.25/20.37  tff(c_1185, plain, (~v1_xboole_0('#skF_11') | ~v1_funct_2('#skF_11', '#skF_9', '#skF_10') | ~v1_funct_1('#skF_11') | v1_xboole_0('#skF_10') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_122, c_1178])).
% 29.25/20.37  tff(c_1198, plain, (~v1_xboole_0('#skF_11') | v1_xboole_0('#skF_10') | v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_124, c_1185])).
% 29.25/20.37  tff(c_1199, plain, (~v1_xboole_0('#skF_11') | v1_xboole_0('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_128, c_1198])).
% 29.25/20.37  tff(c_1206, plain, (~v1_xboole_0('#skF_11')), inference(splitLeft, [status(thm)], [c_1199])).
% 29.25/20.37  tff(c_363, plain, (![A_180, B_179]: (~r1_tarski(A_180, B_179) | v1_xboole_0(A_180) | ~v1_xboole_0(B_179))), inference(resolution, [status(thm)], [c_359, c_22])).
% 29.25/20.37  tff(c_2251, plain, (v1_xboole_0('#skF_11') | ~v1_xboole_0(k2_zfmisc_1('#skF_9', k1_relat_1('#skF_12')))), inference(resolution, [status(thm)], [c_2130, c_363])).
% 29.25/20.37  tff(c_2263, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_9', k1_relat_1('#skF_12')))), inference(negUnitSimplification, [status(thm)], [c_1206, c_2251])).
% 29.25/20.37  tff(c_30576, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_9', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30565, c_2263])).
% 29.25/20.37  tff(c_30589, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_26, c_30576])).
% 29.25/20.37  tff(c_31385, plain, (![A_719]: (r2_hidden(k1_funct_1('#skF_11', A_719), k1_relat_1('#skF_12')) | ~m1_subset_1(A_719, '#skF_9'))), inference(splitRight, [status(thm)], [c_17279])).
% 29.25/20.37  tff(c_50, plain, (![A_30, D_69]: (r2_hidden(k1_funct_1(A_30, D_69), k2_relat_1(A_30)) | ~r2_hidden(D_69, k1_relat_1(A_30)) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_132])).
% 29.25/20.37  tff(c_12722, plain, (r2_hidden(k1_xboole_0, k2_relat_1('#skF_12')) | ~r2_hidden(k1_funct_1('#skF_11', '#skF_13'), k1_relat_1('#skF_12')) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_12710, c_50])).
% 29.25/20.37  tff(c_12732, plain, (r2_hidden(k1_xboole_0, k2_relat_1('#skF_12')) | ~r2_hidden(k1_funct_1('#skF_11', '#skF_13'), k1_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_120, c_12722])).
% 29.25/20.37  tff(c_16524, plain, (~r2_hidden(k1_funct_1('#skF_11', '#skF_13'), k1_relat_1('#skF_12'))), inference(splitLeft, [status(thm)], [c_12732])).
% 29.25/20.37  tff(c_31392, plain, (~m1_subset_1('#skF_13', '#skF_9')), inference(resolution, [status(thm)], [c_31385, c_16524])).
% 29.25/20.37  tff(c_31435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_31392])).
% 29.25/20.37  tff(c_31437, plain, (r2_hidden(k1_funct_1('#skF_11', '#skF_13'), k1_relat_1('#skF_12'))), inference(splitRight, [status(thm)], [c_12732])).
% 29.25/20.37  tff(c_92, plain, (![A_92, B_93, C_95]: (k7_partfun1(A_92, B_93, C_95)=k1_funct_1(B_93, C_95) | ~r2_hidden(C_95, k1_relat_1(B_93)) | ~v1_funct_1(B_93) | ~v5_relat_1(B_93, A_92) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_193])).
% 29.25/20.37  tff(c_31607, plain, (![A_92]: (k7_partfun1(A_92, '#skF_12', k1_funct_1('#skF_11', '#skF_13'))=k1_funct_1('#skF_12', k1_funct_1('#skF_11', '#skF_13')) | ~v1_funct_1('#skF_12') | ~v5_relat_1('#skF_12', A_92) | ~v1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_31437, c_92])).
% 29.25/20.37  tff(c_111682, plain, (![A_1171]: (k7_partfun1(A_1171, '#skF_12', k1_funct_1('#skF_11', '#skF_13'))=k1_xboole_0 | ~v5_relat_1('#skF_12', A_1171))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_120, c_12710, c_31607])).
% 29.25/20.37  tff(c_12711, plain, (k1_funct_1(k8_funct_2('#skF_9', '#skF_10', '#skF_8', '#skF_11', '#skF_12'), '#skF_13')=k1_funct_1('#skF_12', k1_funct_1('#skF_11', '#skF_13'))), inference(splitRight, [status(thm)], [c_11517])).
% 29.25/20.37  tff(c_12932, plain, (k1_funct_1(k8_funct_2('#skF_9', '#skF_10', '#skF_8', '#skF_11', '#skF_12'), '#skF_13')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12710, c_12711])).
% 29.25/20.37  tff(c_12933, plain, (k7_partfun1('#skF_8', '#skF_12', k1_funct_1('#skF_11', '#skF_13'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12932, c_110])).
% 29.25/20.37  tff(c_111688, plain, (~v5_relat_1('#skF_12', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_111682, c_12933])).
% 29.25/20.37  tff(c_111705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_442, c_111688])).
% 29.25/20.37  tff(c_111706, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_1199])).
% 29.25/20.37  tff(c_111713, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_111706, c_8])).
% 29.25/20.37  tff(c_111718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_111713])).
% 29.25/20.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.25/20.37  
% 29.25/20.37  Inference rules
% 29.25/20.37  ----------------------
% 29.25/20.37  #Ref     : 3
% 29.25/20.37  #Sup     : 26634
% 29.25/20.37  #Fact    : 0
% 29.25/20.37  #Define  : 0
% 29.25/20.37  #Split   : 45
% 29.25/20.37  #Chain   : 0
% 29.25/20.37  #Close   : 0
% 29.25/20.37  
% 29.25/20.37  Ordering : KBO
% 29.25/20.37  
% 29.25/20.37  Simplification rules
% 29.25/20.37  ----------------------
% 29.25/20.37  #Subsume      : 11191
% 29.25/20.37  #Demod        : 31230
% 29.25/20.37  #Tautology    : 10215
% 29.25/20.37  #SimpNegUnit  : 3180
% 29.25/20.37  #BackRed      : 199
% 29.25/20.37  
% 29.25/20.37  #Partial instantiations: 0
% 29.25/20.37  #Strategies tried      : 1
% 29.25/20.37  
% 29.25/20.37  Timing (in seconds)
% 29.25/20.37  ----------------------
% 29.25/20.37  Preprocessing        : 0.44
% 29.25/20.37  Parsing              : 0.23
% 29.25/20.37  CNF conversion       : 0.04
% 29.25/20.37  Main loop            : 19.16
% 29.25/20.37  Inferencing          : 2.50
% 29.25/20.37  Reduction            : 9.22
% 29.25/20.37  Demodulation         : 7.15
% 29.25/20.37  BG Simplification    : 0.22
% 29.25/20.37  Subsumption          : 6.45
% 29.25/20.37  Abstraction          : 0.44
% 29.25/20.37  MUC search           : 0.00
% 29.25/20.37  Cooper               : 0.00
% 29.25/20.37  Total                : 19.65
% 29.25/20.37  Index Insertion      : 0.00
% 29.25/20.37  Index Deletion       : 0.00
% 29.25/20.37  Index Matching       : 0.00
% 29.25/20.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
