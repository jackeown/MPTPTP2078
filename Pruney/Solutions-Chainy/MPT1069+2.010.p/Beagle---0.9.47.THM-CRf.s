%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:46 EST 2020

% Result     : Theorem 8.97s
% Output     : CNFRefutation 8.97s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 413 expanded)
%              Number of leaves         :   46 ( 163 expanded)
%              Depth                    :   14
%              Number of atoms          :  261 (1444 expanded)
%              Number of equality atoms :   71 ( 360 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_226,negated_conjecture,(
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

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_189,axiom,(
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

tff(f_83,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_165,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_154,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_102,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_92,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_387,plain,(
    ! [C_137,B_138,A_139] :
      ( v5_relat_1(C_137,B_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_405,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_387])).

tff(c_241,plain,(
    ! [C_111,A_112,B_113] :
      ( v1_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_257,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_92,c_241])).

tff(c_94,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_90,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_100,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_98,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_96,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_831,plain,(
    ! [A_193,B_194,C_195] :
      ( k2_relset_1(A_193,B_194,C_195) = k2_relat_1(C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_853,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_831])).

tff(c_782,plain,(
    ! [A_190,B_191,C_192] :
      ( k1_relset_1(A_190,B_191,C_192) = k1_relat_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_803,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_92,c_782])).

tff(c_88,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_807,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_88])).

tff(c_859,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_853,c_807])).

tff(c_2641,plain,(
    ! [E_339,F_344,A_341,C_340,B_343,D_342] :
      ( k1_funct_1(k8_funct_2(B_343,C_340,A_341,D_342,E_339),F_344) = k1_funct_1(E_339,k1_funct_1(D_342,F_344))
      | k1_xboole_0 = B_343
      | ~ r1_tarski(k2_relset_1(B_343,C_340,D_342),k1_relset_1(C_340,A_341,E_339))
      | ~ m1_subset_1(F_344,B_343)
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(C_340,A_341)))
      | ~ v1_funct_1(E_339)
      | ~ m1_subset_1(D_342,k1_zfmisc_1(k2_zfmisc_1(B_343,C_340)))
      | ~ v1_funct_2(D_342,B_343,C_340)
      | ~ v1_funct_1(D_342)
      | v1_xboole_0(C_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_2661,plain,(
    ! [B_343,D_342,F_344] :
      ( k1_funct_1(k8_funct_2(B_343,'#skF_5','#skF_3',D_342,'#skF_7'),F_344) = k1_funct_1('#skF_7',k1_funct_1(D_342,F_344))
      | k1_xboole_0 = B_343
      | ~ r1_tarski(k2_relset_1(B_343,'#skF_5',D_342),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_344,B_343)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_342,k1_zfmisc_1(k2_zfmisc_1(B_343,'#skF_5')))
      | ~ v1_funct_2(D_342,B_343,'#skF_5')
      | ~ v1_funct_1(D_342)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_2641])).

tff(c_2690,plain,(
    ! [B_343,D_342,F_344] :
      ( k1_funct_1(k8_funct_2(B_343,'#skF_5','#skF_3',D_342,'#skF_7'),F_344) = k1_funct_1('#skF_7',k1_funct_1(D_342,F_344))
      | k1_xboole_0 = B_343
      | ~ r1_tarski(k2_relset_1(B_343,'#skF_5',D_342),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_344,B_343)
      | ~ m1_subset_1(D_342,k1_zfmisc_1(k2_zfmisc_1(B_343,'#skF_5')))
      | ~ v1_funct_2(D_342,B_343,'#skF_5')
      | ~ v1_funct_1(D_342)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_2661])).

tff(c_2911,plain,(
    ! [B_363,D_364,F_365] :
      ( k1_funct_1(k8_funct_2(B_363,'#skF_5','#skF_3',D_364,'#skF_7'),F_365) = k1_funct_1('#skF_7',k1_funct_1(D_364,F_365))
      | k1_xboole_0 = B_363
      | ~ r1_tarski(k2_relset_1(B_363,'#skF_5',D_364),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_365,B_363)
      | ~ m1_subset_1(D_364,k1_zfmisc_1(k2_zfmisc_1(B_363,'#skF_5')))
      | ~ v1_funct_2(D_364,B_363,'#skF_5')
      | ~ v1_funct_1(D_364) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_2690])).

tff(c_2916,plain,(
    ! [F_365] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_365) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_365))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_365,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_2911])).

tff(c_2924,plain,(
    ! [F_365] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_365) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_365))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_365,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_96,c_859,c_2916])).

tff(c_2925,plain,(
    ! [F_365] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_365) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_365))
      | ~ m1_subset_1(F_365,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2924])).

tff(c_40,plain,(
    ! [A_19,B_22] :
      ( k1_funct_1(A_19,B_22) = k1_xboole_0
      | r2_hidden(B_22,k1_relat_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2480,plain,(
    ! [A_331,B_332,C_333] :
      ( k7_partfun1(A_331,B_332,C_333) = k1_funct_1(B_332,C_333)
      | ~ r2_hidden(C_333,k1_relat_1(B_332))
      | ~ v1_funct_1(B_332)
      | ~ v5_relat_1(B_332,A_331)
      | ~ v1_relat_1(B_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_6864,plain,(
    ! [A_617,A_618,B_619] :
      ( k7_partfun1(A_617,A_618,B_619) = k1_funct_1(A_618,B_619)
      | ~ v5_relat_1(A_618,A_617)
      | k1_funct_1(A_618,B_619) = k1_xboole_0
      | ~ v1_funct_1(A_618)
      | ~ v1_relat_1(A_618) ) ),
    inference(resolution,[status(thm)],[c_40,c_2480])).

tff(c_6886,plain,(
    ! [B_619] :
      ( k7_partfun1('#skF_3','#skF_7',B_619) = k1_funct_1('#skF_7',B_619)
      | k1_funct_1('#skF_7',B_619) = k1_xboole_0
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_405,c_6864])).

tff(c_6997,plain,(
    ! [B_625] :
      ( k7_partfun1('#skF_3','#skF_7',B_625) = k1_funct_1('#skF_7',B_625)
      | k1_funct_1('#skF_7',B_625) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_94,c_6886])).

tff(c_84,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_7003,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6997,c_84])).

tff(c_7829,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_7003])).

tff(c_8580,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2925,c_7829])).

tff(c_8584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_8580])).

tff(c_8585,plain,(
    k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7003])).

tff(c_258,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_241])).

tff(c_804,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_782])).

tff(c_2071,plain,(
    ! [B_307,A_308,C_309] :
      ( k1_xboole_0 = B_307
      | k1_relset_1(A_308,B_307,C_309) = A_308
      | ~ v1_funct_2(C_309,A_308,B_307)
      | ~ m1_subset_1(C_309,k1_zfmisc_1(k2_zfmisc_1(A_308,B_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2090,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_2071])).

tff(c_2101,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_804,c_2090])).

tff(c_2102,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2101])).

tff(c_2113,plain,(
    ! [B_22] :
      ( k1_funct_1('#skF_6',B_22) = k1_xboole_0
      | r2_hidden(B_22,'#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2102,c_40])).

tff(c_2142,plain,(
    ! [B_311] :
      ( k1_funct_1('#skF_6',B_311) = k1_xboole_0
      | r2_hidden(B_311,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_100,c_2113])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2154,plain,(
    ! [B_311] :
      ( ~ v1_xboole_0('#skF_4')
      | k1_funct_1('#skF_6',B_311) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2142,c_2])).

tff(c_2176,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2154])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1837,plain,(
    ! [B_290,A_291] :
      ( r2_hidden(k1_funct_1(B_290,A_291),k2_relat_1(B_290))
      | ~ r2_hidden(A_291,k1_relat_1(B_290))
      | ~ v1_funct_1(B_290)
      | ~ v1_relat_1(B_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1843,plain,(
    ! [B_290,A_291,B_6] :
      ( r2_hidden(k1_funct_1(B_290,A_291),B_6)
      | ~ r1_tarski(k2_relat_1(B_290),B_6)
      | ~ r2_hidden(A_291,k1_relat_1(B_290))
      | ~ v1_funct_1(B_290)
      | ~ v1_relat_1(B_290) ) ),
    inference(resolution,[status(thm)],[c_1837,c_6])).

tff(c_42,plain,(
    ! [B_25,A_24] :
      ( r2_hidden(k1_funct_1(B_25,A_24),k2_relat_1(B_25))
      | ~ r2_hidden(A_24,k1_relat_1(B_25))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8599,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_7'))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_8585,c_42])).

tff(c_8609,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_7'))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_94,c_8599])).

tff(c_9486,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_8609])).

tff(c_9492,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1843,c_9486])).

tff(c_9507,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_100,c_2102,c_859,c_9492])).

tff(c_9549,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_9507])).

tff(c_9556,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_9549])).

tff(c_9558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2176,c_9556])).

tff(c_9560,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_8609])).

tff(c_74,plain,(
    ! [A_49,B_50,C_52] :
      ( k7_partfun1(A_49,B_50,C_52) = k1_funct_1(B_50,C_52)
      | ~ r2_hidden(C_52,k1_relat_1(B_50))
      | ~ v1_funct_1(B_50)
      | ~ v5_relat_1(B_50,A_49)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_9580,plain,(
    ! [A_49] :
      ( k7_partfun1(A_49,'#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_49)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_9560,c_74])).

tff(c_9746,plain,(
    ! [A_692] :
      ( k7_partfun1(A_692,'#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_xboole_0
      | ~ v5_relat_1('#skF_7',A_692) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_94,c_8585,c_9580])).

tff(c_8586,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') = k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_7003])).

tff(c_9355,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8585,c_8586])).

tff(c_9356,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9355,c_84])).

tff(c_9752,plain,(
    ~ v5_relat_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9746,c_9356])).

tff(c_9768,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_9752])).

tff(c_9770,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2154])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_156,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_2'(A_94,B_95),A_94)
      | r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_160,plain,(
    ! [A_94,B_95] :
      ( ~ v1_xboole_0(A_94)
      | r1_tarski(A_94,B_95) ) ),
    inference(resolution,[status(thm)],[c_156,c_2])).

tff(c_169,plain,(
    ! [B_100,A_101] :
      ( B_100 = A_101
      | ~ r1_tarski(B_100,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_199,plain,(
    ! [B_104,A_105] :
      ( B_104 = A_105
      | ~ r1_tarski(B_104,A_105)
      | ~ v1_xboole_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_160,c_169])).

tff(c_221,plain,(
    ! [B_106,A_107] :
      ( B_106 = A_107
      | ~ v1_xboole_0(B_106)
      | ~ v1_xboole_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_160,c_199])).

tff(c_224,plain,(
    ! [A_107] :
      ( k1_xboole_0 = A_107
      | ~ v1_xboole_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_12,c_221])).

tff(c_9786,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9770,c_224])).

tff(c_9801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_9786])).

tff(c_9802,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2101])).

tff(c_9848,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9802,c_12])).

tff(c_9851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_9848])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:40:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.97/3.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.97/3.16  
% 8.97/3.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.97/3.16  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 8.97/3.16  
% 8.97/3.16  %Foreground sorts:
% 8.97/3.16  
% 8.97/3.16  
% 8.97/3.16  %Background operators:
% 8.97/3.16  
% 8.97/3.16  
% 8.97/3.16  %Foreground operators:
% 8.97/3.16  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.97/3.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.97/3.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.97/3.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.97/3.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.97/3.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.97/3.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.97/3.16  tff('#skF_7', type, '#skF_7': $i).
% 8.97/3.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.97/3.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.97/3.16  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 8.97/3.16  tff('#skF_5', type, '#skF_5': $i).
% 8.97/3.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.97/3.16  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 8.97/3.16  tff('#skF_6', type, '#skF_6': $i).
% 8.97/3.16  tff('#skF_3', type, '#skF_3': $i).
% 8.97/3.16  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.97/3.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.97/3.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.97/3.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.97/3.16  tff('#skF_8', type, '#skF_8': $i).
% 8.97/3.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.97/3.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.97/3.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.97/3.16  tff('#skF_4', type, '#skF_4': $i).
% 8.97/3.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.97/3.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.97/3.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.97/3.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.97/3.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.97/3.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.97/3.16  
% 8.97/3.18  tff(f_226, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 8.97/3.18  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.97/3.18  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.97/3.18  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.97/3.18  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.97/3.18  tff(f_189, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 8.97/3.18  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 8.97/3.18  tff(f_165, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 8.97/3.18  tff(f_154, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.97/3.18  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.97/3.18  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 8.97/3.18  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 8.97/3.18  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.97/3.18  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.97/3.18  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.97/3.18  tff(c_102, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.97/3.18  tff(c_86, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.97/3.18  tff(c_92, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.97/3.18  tff(c_387, plain, (![C_137, B_138, A_139]: (v5_relat_1(C_137, B_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.97/3.18  tff(c_405, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_92, c_387])).
% 8.97/3.18  tff(c_241, plain, (![C_111, A_112, B_113]: (v1_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.97/3.18  tff(c_257, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_92, c_241])).
% 8.97/3.18  tff(c_94, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.97/3.18  tff(c_90, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.97/3.18  tff(c_100, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.97/3.18  tff(c_98, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.97/3.18  tff(c_96, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.97/3.18  tff(c_831, plain, (![A_193, B_194, C_195]: (k2_relset_1(A_193, B_194, C_195)=k2_relat_1(C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.97/3.18  tff(c_853, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_96, c_831])).
% 8.97/3.18  tff(c_782, plain, (![A_190, B_191, C_192]: (k1_relset_1(A_190, B_191, C_192)=k1_relat_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.97/3.18  tff(c_803, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_92, c_782])).
% 8.97/3.18  tff(c_88, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.97/3.18  tff(c_807, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_803, c_88])).
% 8.97/3.18  tff(c_859, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_853, c_807])).
% 8.97/3.18  tff(c_2641, plain, (![E_339, F_344, A_341, C_340, B_343, D_342]: (k1_funct_1(k8_funct_2(B_343, C_340, A_341, D_342, E_339), F_344)=k1_funct_1(E_339, k1_funct_1(D_342, F_344)) | k1_xboole_0=B_343 | ~r1_tarski(k2_relset_1(B_343, C_340, D_342), k1_relset_1(C_340, A_341, E_339)) | ~m1_subset_1(F_344, B_343) | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(C_340, A_341))) | ~v1_funct_1(E_339) | ~m1_subset_1(D_342, k1_zfmisc_1(k2_zfmisc_1(B_343, C_340))) | ~v1_funct_2(D_342, B_343, C_340) | ~v1_funct_1(D_342) | v1_xboole_0(C_340))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.97/3.18  tff(c_2661, plain, (![B_343, D_342, F_344]: (k1_funct_1(k8_funct_2(B_343, '#skF_5', '#skF_3', D_342, '#skF_7'), F_344)=k1_funct_1('#skF_7', k1_funct_1(D_342, F_344)) | k1_xboole_0=B_343 | ~r1_tarski(k2_relset_1(B_343, '#skF_5', D_342), k1_relat_1('#skF_7')) | ~m1_subset_1(F_344, B_343) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_342, k1_zfmisc_1(k2_zfmisc_1(B_343, '#skF_5'))) | ~v1_funct_2(D_342, B_343, '#skF_5') | ~v1_funct_1(D_342) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_803, c_2641])).
% 8.97/3.18  tff(c_2690, plain, (![B_343, D_342, F_344]: (k1_funct_1(k8_funct_2(B_343, '#skF_5', '#skF_3', D_342, '#skF_7'), F_344)=k1_funct_1('#skF_7', k1_funct_1(D_342, F_344)) | k1_xboole_0=B_343 | ~r1_tarski(k2_relset_1(B_343, '#skF_5', D_342), k1_relat_1('#skF_7')) | ~m1_subset_1(F_344, B_343) | ~m1_subset_1(D_342, k1_zfmisc_1(k2_zfmisc_1(B_343, '#skF_5'))) | ~v1_funct_2(D_342, B_343, '#skF_5') | ~v1_funct_1(D_342) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_2661])).
% 8.97/3.18  tff(c_2911, plain, (![B_363, D_364, F_365]: (k1_funct_1(k8_funct_2(B_363, '#skF_5', '#skF_3', D_364, '#skF_7'), F_365)=k1_funct_1('#skF_7', k1_funct_1(D_364, F_365)) | k1_xboole_0=B_363 | ~r1_tarski(k2_relset_1(B_363, '#skF_5', D_364), k1_relat_1('#skF_7')) | ~m1_subset_1(F_365, B_363) | ~m1_subset_1(D_364, k1_zfmisc_1(k2_zfmisc_1(B_363, '#skF_5'))) | ~v1_funct_2(D_364, B_363, '#skF_5') | ~v1_funct_1(D_364))), inference(negUnitSimplification, [status(thm)], [c_102, c_2690])).
% 8.97/3.18  tff(c_2916, plain, (![F_365]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_365)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_365)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~m1_subset_1(F_365, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_853, c_2911])).
% 8.97/3.18  tff(c_2924, plain, (![F_365]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_365)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_365)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_365, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_96, c_859, c_2916])).
% 8.97/3.18  tff(c_2925, plain, (![F_365]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_365)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_365)) | ~m1_subset_1(F_365, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_86, c_2924])).
% 8.97/3.18  tff(c_40, plain, (![A_19, B_22]: (k1_funct_1(A_19, B_22)=k1_xboole_0 | r2_hidden(B_22, k1_relat_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.97/3.18  tff(c_2480, plain, (![A_331, B_332, C_333]: (k7_partfun1(A_331, B_332, C_333)=k1_funct_1(B_332, C_333) | ~r2_hidden(C_333, k1_relat_1(B_332)) | ~v1_funct_1(B_332) | ~v5_relat_1(B_332, A_331) | ~v1_relat_1(B_332))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.97/3.18  tff(c_6864, plain, (![A_617, A_618, B_619]: (k7_partfun1(A_617, A_618, B_619)=k1_funct_1(A_618, B_619) | ~v5_relat_1(A_618, A_617) | k1_funct_1(A_618, B_619)=k1_xboole_0 | ~v1_funct_1(A_618) | ~v1_relat_1(A_618))), inference(resolution, [status(thm)], [c_40, c_2480])).
% 8.97/3.18  tff(c_6886, plain, (![B_619]: (k7_partfun1('#skF_3', '#skF_7', B_619)=k1_funct_1('#skF_7', B_619) | k1_funct_1('#skF_7', B_619)=k1_xboole_0 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_405, c_6864])).
% 8.97/3.18  tff(c_6997, plain, (![B_625]: (k7_partfun1('#skF_3', '#skF_7', B_625)=k1_funct_1('#skF_7', B_625) | k1_funct_1('#skF_7', B_625)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_257, c_94, c_6886])).
% 8.97/3.18  tff(c_84, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.97/3.18  tff(c_7003, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6997, c_84])).
% 8.97/3.18  tff(c_7829, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_7003])).
% 8.97/3.18  tff(c_8580, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2925, c_7829])).
% 8.97/3.18  tff(c_8584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_8580])).
% 8.97/3.18  tff(c_8585, plain, (k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_7003])).
% 8.97/3.18  tff(c_258, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_96, c_241])).
% 8.97/3.18  tff(c_804, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_96, c_782])).
% 8.97/3.18  tff(c_2071, plain, (![B_307, A_308, C_309]: (k1_xboole_0=B_307 | k1_relset_1(A_308, B_307, C_309)=A_308 | ~v1_funct_2(C_309, A_308, B_307) | ~m1_subset_1(C_309, k1_zfmisc_1(k2_zfmisc_1(A_308, B_307))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.97/3.18  tff(c_2090, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_96, c_2071])).
% 8.97/3.18  tff(c_2101, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_804, c_2090])).
% 8.97/3.18  tff(c_2102, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_2101])).
% 8.97/3.18  tff(c_2113, plain, (![B_22]: (k1_funct_1('#skF_6', B_22)=k1_xboole_0 | r2_hidden(B_22, '#skF_4') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2102, c_40])).
% 8.97/3.18  tff(c_2142, plain, (![B_311]: (k1_funct_1('#skF_6', B_311)=k1_xboole_0 | r2_hidden(B_311, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_100, c_2113])).
% 8.97/3.18  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.97/3.18  tff(c_2154, plain, (![B_311]: (~v1_xboole_0('#skF_4') | k1_funct_1('#skF_6', B_311)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2142, c_2])).
% 8.97/3.18  tff(c_2176, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_2154])).
% 8.97/3.18  tff(c_26, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.97/3.18  tff(c_1837, plain, (![B_290, A_291]: (r2_hidden(k1_funct_1(B_290, A_291), k2_relat_1(B_290)) | ~r2_hidden(A_291, k1_relat_1(B_290)) | ~v1_funct_1(B_290) | ~v1_relat_1(B_290))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.97/3.18  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.97/3.18  tff(c_1843, plain, (![B_290, A_291, B_6]: (r2_hidden(k1_funct_1(B_290, A_291), B_6) | ~r1_tarski(k2_relat_1(B_290), B_6) | ~r2_hidden(A_291, k1_relat_1(B_290)) | ~v1_funct_1(B_290) | ~v1_relat_1(B_290))), inference(resolution, [status(thm)], [c_1837, c_6])).
% 8.97/3.18  tff(c_42, plain, (![B_25, A_24]: (r2_hidden(k1_funct_1(B_25, A_24), k2_relat_1(B_25)) | ~r2_hidden(A_24, k1_relat_1(B_25)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.97/3.18  tff(c_8599, plain, (r2_hidden(k1_xboole_0, k2_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_8585, c_42])).
% 8.97/3.18  tff(c_8609, plain, (r2_hidden(k1_xboole_0, k2_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_94, c_8599])).
% 8.97/3.18  tff(c_9486, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_8609])).
% 8.97/3.18  tff(c_9492, plain, (~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1843, c_9486])).
% 8.97/3.18  tff(c_9507, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_258, c_100, c_2102, c_859, c_9492])).
% 8.97/3.18  tff(c_9549, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_9507])).
% 8.97/3.18  tff(c_9556, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_9549])).
% 8.97/3.18  tff(c_9558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2176, c_9556])).
% 8.97/3.18  tff(c_9560, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_8609])).
% 8.97/3.18  tff(c_74, plain, (![A_49, B_50, C_52]: (k7_partfun1(A_49, B_50, C_52)=k1_funct_1(B_50, C_52) | ~r2_hidden(C_52, k1_relat_1(B_50)) | ~v1_funct_1(B_50) | ~v5_relat_1(B_50, A_49) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.97/3.18  tff(c_9580, plain, (![A_49]: (k7_partfun1(A_49, '#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_49) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_9560, c_74])).
% 8.97/3.18  tff(c_9746, plain, (![A_692]: (k7_partfun1(A_692, '#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_xboole_0 | ~v5_relat_1('#skF_7', A_692))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_94, c_8585, c_9580])).
% 8.97/3.18  tff(c_8586, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_7003])).
% 8.97/3.18  tff(c_9355, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8585, c_8586])).
% 8.97/3.18  tff(c_9356, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9355, c_84])).
% 8.97/3.18  tff(c_9752, plain, (~v5_relat_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9746, c_9356])).
% 8.97/3.18  tff(c_9768, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_405, c_9752])).
% 8.97/3.18  tff(c_9770, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_2154])).
% 8.97/3.18  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.97/3.18  tff(c_156, plain, (![A_94, B_95]: (r2_hidden('#skF_2'(A_94, B_95), A_94) | r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.97/3.18  tff(c_160, plain, (![A_94, B_95]: (~v1_xboole_0(A_94) | r1_tarski(A_94, B_95))), inference(resolution, [status(thm)], [c_156, c_2])).
% 8.97/3.18  tff(c_169, plain, (![B_100, A_101]: (B_100=A_101 | ~r1_tarski(B_100, A_101) | ~r1_tarski(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.97/3.18  tff(c_199, plain, (![B_104, A_105]: (B_104=A_105 | ~r1_tarski(B_104, A_105) | ~v1_xboole_0(A_105))), inference(resolution, [status(thm)], [c_160, c_169])).
% 8.97/3.18  tff(c_221, plain, (![B_106, A_107]: (B_106=A_107 | ~v1_xboole_0(B_106) | ~v1_xboole_0(A_107))), inference(resolution, [status(thm)], [c_160, c_199])).
% 8.97/3.18  tff(c_224, plain, (![A_107]: (k1_xboole_0=A_107 | ~v1_xboole_0(A_107))), inference(resolution, [status(thm)], [c_12, c_221])).
% 8.97/3.18  tff(c_9786, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_9770, c_224])).
% 8.97/3.18  tff(c_9801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_9786])).
% 8.97/3.18  tff(c_9802, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2101])).
% 8.97/3.18  tff(c_9848, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9802, c_12])).
% 8.97/3.18  tff(c_9851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_9848])).
% 8.97/3.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.97/3.18  
% 8.97/3.18  Inference rules
% 8.97/3.18  ----------------------
% 8.97/3.18  #Ref     : 3
% 8.97/3.18  #Sup     : 2179
% 8.97/3.18  #Fact    : 0
% 8.97/3.18  #Define  : 0
% 8.97/3.18  #Split   : 54
% 8.97/3.18  #Chain   : 0
% 8.97/3.18  #Close   : 0
% 8.97/3.18  
% 8.97/3.18  Ordering : KBO
% 8.97/3.18  
% 8.97/3.18  Simplification rules
% 8.97/3.18  ----------------------
% 8.97/3.18  #Subsume      : 658
% 8.97/3.18  #Demod        : 1561
% 8.97/3.18  #Tautology    : 620
% 8.97/3.18  #SimpNegUnit  : 125
% 8.97/3.18  #BackRed      : 55
% 8.97/3.18  
% 8.97/3.18  #Partial instantiations: 0
% 8.97/3.18  #Strategies tried      : 1
% 8.97/3.18  
% 8.97/3.18  Timing (in seconds)
% 8.97/3.18  ----------------------
% 8.97/3.19  Preprocessing        : 0.41
% 8.97/3.19  Parsing              : 0.21
% 8.97/3.19  CNF conversion       : 0.03
% 8.97/3.19  Main loop            : 2.00
% 8.97/3.19  Inferencing          : 0.55
% 8.97/3.19  Reduction            : 0.70
% 8.97/3.19  Demodulation         : 0.49
% 8.97/3.19  BG Simplification    : 0.06
% 8.97/3.19  Subsumption          : 0.55
% 8.97/3.19  Abstraction          : 0.08
% 8.97/3.19  MUC search           : 0.00
% 8.97/3.19  Cooper               : 0.00
% 8.97/3.19  Total                : 2.44
% 8.97/3.19  Index Insertion      : 0.00
% 8.97/3.19  Index Deletion       : 0.00
% 8.97/3.19  Index Matching       : 0.00
% 8.97/3.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
