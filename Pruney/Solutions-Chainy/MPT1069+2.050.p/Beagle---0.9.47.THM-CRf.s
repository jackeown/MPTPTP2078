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
% DateTime   : Thu Dec  3 10:17:52 EST 2020

% Result     : Theorem 5.78s
% Output     : CNFRefutation 6.12s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 730 expanded)
%              Number of leaves         :   43 ( 266 expanded)
%              Depth                    :   22
%              Number of atoms          :  338 (2423 expanded)
%              Number of equality atoms :   75 ( 506 expanded)
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

tff(f_183,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_158,axiom,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_123,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_62,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_210,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_relset_1(A_104,B_105,C_106) = k2_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_223,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_210])).

tff(c_183,plain,(
    ! [A_94,B_95,C_96] :
      ( k1_relset_1(A_94,B_95,C_96) = k1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_195,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_183])).

tff(c_60,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_197,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_60])).

tff(c_228,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_197])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_70,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_3754,plain,(
    ! [C_551,B_548,A_547,F_549,D_550,E_546] :
      ( k1_funct_1(k8_funct_2(B_548,C_551,A_547,D_550,E_546),F_549) = k1_funct_1(E_546,k1_funct_1(D_550,F_549))
      | k1_xboole_0 = B_548
      | ~ r1_tarski(k2_relset_1(B_548,C_551,D_550),k1_relset_1(C_551,A_547,E_546))
      | ~ m1_subset_1(F_549,B_548)
      | ~ m1_subset_1(E_546,k1_zfmisc_1(k2_zfmisc_1(C_551,A_547)))
      | ~ v1_funct_1(E_546)
      | ~ m1_subset_1(D_550,k1_zfmisc_1(k2_zfmisc_1(B_548,C_551)))
      | ~ v1_funct_2(D_550,B_548,C_551)
      | ~ v1_funct_1(D_550)
      | v1_xboole_0(C_551) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3758,plain,(
    ! [A_547,E_546,F_549] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_547,'#skF_5',E_546),F_549) = k1_funct_1(E_546,k1_funct_1('#skF_5',F_549))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',A_547,E_546))
      | ~ m1_subset_1(F_549,'#skF_3')
      | ~ m1_subset_1(E_546,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_547)))
      | ~ v1_funct_1(E_546)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_3754])).

tff(c_3767,plain,(
    ! [A_547,E_546,F_549] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_547,'#skF_5',E_546),F_549) = k1_funct_1(E_546,k1_funct_1('#skF_5',F_549))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',A_547,E_546))
      | ~ m1_subset_1(F_549,'#skF_3')
      | ~ m1_subset_1(E_546,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_547)))
      | ~ v1_funct_1(E_546)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_3758])).

tff(c_3924,plain,(
    ! [A_566,E_567,F_568] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_566,'#skF_5',E_567),F_568) = k1_funct_1(E_567,k1_funct_1('#skF_5',F_568))
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',A_566,E_567))
      | ~ m1_subset_1(F_568,'#skF_3')
      | ~ m1_subset_1(E_567,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_566)))
      | ~ v1_funct_1(E_567) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_58,c_3767])).

tff(c_3926,plain,(
    ! [F_568] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_568) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_568))
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_568,'#skF_3')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_3924])).

tff(c_3952,plain,(
    ! [F_576] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_576) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_576))
      | ~ m1_subset_1(F_576,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_228,c_3926])).

tff(c_86,plain,(
    ! [B_70,A_71] :
      ( v1_xboole_0(B_70)
      | ~ m1_subset_1(B_70,A_71)
      | ~ v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_98,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_86])).

tff(c_99,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,A_8)
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_148,plain,(
    ! [C_85,B_86,A_87] :
      ( r2_hidden(C_85,B_86)
      | ~ r2_hidden(C_85,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_283,plain,(
    ! [B_113,B_114,A_115] :
      ( r2_hidden(B_113,B_114)
      | ~ r1_tarski(A_115,B_114)
      | ~ m1_subset_1(B_113,A_115)
      | v1_xboole_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_14,c_148])).

tff(c_288,plain,(
    ! [B_113] :
      ( r2_hidden(B_113,k1_relat_1('#skF_6'))
      | ~ m1_subset_1(B_113,k2_relat_1('#skF_5'))
      | v1_xboole_0(k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_228,c_283])).

tff(c_311,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    ! [B_67,A_68] :
      ( ~ v1_xboole_0(B_67)
      | B_67 = A_68
      | ~ v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_79,plain,(
    ! [A_68] :
      ( k1_xboole_0 = A_68
      | ~ v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_317,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_311,c_79])).

tff(c_320,plain,(
    r1_tarski(k1_xboole_0,k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_228])).

tff(c_321,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_223])).

tff(c_1760,plain,(
    ! [C_296,B_293,D_295,E_291,F_294,A_292] :
      ( k1_funct_1(k8_funct_2(B_293,C_296,A_292,D_295,E_291),F_294) = k1_funct_1(E_291,k1_funct_1(D_295,F_294))
      | k1_xboole_0 = B_293
      | ~ r1_tarski(k2_relset_1(B_293,C_296,D_295),k1_relset_1(C_296,A_292,E_291))
      | ~ m1_subset_1(F_294,B_293)
      | ~ m1_subset_1(E_291,k1_zfmisc_1(k2_zfmisc_1(C_296,A_292)))
      | ~ v1_funct_1(E_291)
      | ~ m1_subset_1(D_295,k1_zfmisc_1(k2_zfmisc_1(B_293,C_296)))
      | ~ v1_funct_2(D_295,B_293,C_296)
      | ~ v1_funct_1(D_295)
      | v1_xboole_0(C_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1764,plain,(
    ! [A_292,E_291,F_294] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_292,'#skF_5',E_291),F_294) = k1_funct_1(E_291,k1_funct_1('#skF_5',F_294))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k1_xboole_0,k1_relset_1('#skF_4',A_292,E_291))
      | ~ m1_subset_1(F_294,'#skF_3')
      | ~ m1_subset_1(E_291,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_292)))
      | ~ v1_funct_1(E_291)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_1760])).

tff(c_1773,plain,(
    ! [A_292,E_291,F_294] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_292,'#skF_5',E_291),F_294) = k1_funct_1(E_291,k1_funct_1('#skF_5',F_294))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k1_xboole_0,k1_relset_1('#skF_4',A_292,E_291))
      | ~ m1_subset_1(F_294,'#skF_3')
      | ~ m1_subset_1(E_291,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_292)))
      | ~ v1_funct_1(E_291)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1764])).

tff(c_1787,plain,(
    ! [A_301,E_302,F_303] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_301,'#skF_5',E_302),F_303) = k1_funct_1(E_302,k1_funct_1('#skF_5',F_303))
      | ~ r1_tarski(k1_xboole_0,k1_relset_1('#skF_4',A_301,E_302))
      | ~ m1_subset_1(F_303,'#skF_3')
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_301)))
      | ~ v1_funct_1(E_302) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_58,c_1773])).

tff(c_1801,plain,(
    ! [F_303] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_303) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_303))
      | ~ r1_tarski(k1_xboole_0,k1_relset_1('#skF_4','#skF_2','#skF_6'))
      | ~ m1_subset_1(F_303,'#skF_3')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_64,c_1787])).

tff(c_1808,plain,(
    ! [F_303] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_303) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_303))
      | ~ m1_subset_1(F_303,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_320,c_195,c_1801])).

tff(c_155,plain,(
    ! [C_88,B_89,A_90] :
      ( v5_relat_1(C_88,B_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_167,plain,(
    v5_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_155])).

tff(c_22,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_107,plain,(
    ! [B_74,A_75] :
      ( v1_relat_1(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_114,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_107])).

tff(c_121,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_114])).

tff(c_126,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_1'(A_78,B_79),A_78)
      | r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131,plain,(
    ! [A_78] : r1_tarski(A_78,A_78) ),
    inference(resolution,[status(thm)],[c_126,c_4])).

tff(c_196,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_183])).

tff(c_1333,plain,(
    ! [B_240,A_241,C_242] :
      ( k1_xboole_0 = B_240
      | k1_relset_1(A_241,B_240,C_242) = A_241
      | ~ v1_funct_2(C_242,A_241,B_240)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_241,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1351,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1333])).

tff(c_1359,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_196,c_1351])).

tff(c_1360,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1359])).

tff(c_117,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_107])).

tff(c_124,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_117])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r2_hidden(k1_funct_1(B_16,A_15),k2_relat_1(B_16))
      | ~ r2_hidden(A_15,k1_relat_1(B_16))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_326,plain,(
    ! [A_15] :
      ( r2_hidden(k1_funct_1('#skF_5',A_15),k1_xboole_0)
      | ~ r2_hidden(A_15,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_24])).

tff(c_341,plain,(
    ! [A_121] :
      ( r2_hidden(k1_funct_1('#skF_5',A_121),k1_xboole_0)
      | ~ r2_hidden(A_121,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_72,c_326])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_347,plain,(
    ! [A_121,B_2] :
      ( r2_hidden(k1_funct_1('#skF_5',A_121),B_2)
      | ~ r1_tarski(k1_xboole_0,B_2)
      | ~ r2_hidden(A_121,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_341,c_2])).

tff(c_1383,plain,(
    ! [A_244,B_245] :
      ( r2_hidden(k1_funct_1('#skF_5',A_244),B_245)
      | ~ r1_tarski(k1_xboole_0,B_245)
      | ~ r2_hidden(A_244,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_347])).

tff(c_1515,plain,(
    ! [A_258,B_259,B_260] :
      ( r2_hidden(k1_funct_1('#skF_5',A_258),B_259)
      | ~ r1_tarski(B_260,B_259)
      | ~ r1_tarski(k1_xboole_0,B_260)
      | ~ r2_hidden(A_258,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1383,c_2])).

tff(c_1519,plain,(
    ! [A_258] :
      ( r2_hidden(k1_funct_1('#skF_5',A_258),k1_relat_1('#skF_6'))
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(A_258,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_320,c_1515])).

tff(c_1525,plain,(
    ! [A_258] :
      ( r2_hidden(k1_funct_1('#skF_5',A_258),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_258,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_1519])).

tff(c_1537,plain,(
    ! [A_262,B_263,C_264] :
      ( k7_partfun1(A_262,B_263,C_264) = k1_funct_1(B_263,C_264)
      | ~ r2_hidden(C_264,k1_relat_1(B_263))
      | ~ v1_funct_1(B_263)
      | ~ v5_relat_1(B_263,A_262)
      | ~ v1_relat_1(B_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1539,plain,(
    ! [A_262,A_258] :
      ( k7_partfun1(A_262,'#skF_6',k1_funct_1('#skF_5',A_258)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',A_258))
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_262)
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(A_258,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1525,c_1537])).

tff(c_2080,plain,(
    ! [A_332,A_333] :
      ( k7_partfun1(A_332,'#skF_6',k1_funct_1('#skF_5',A_333)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',A_333))
      | ~ v5_relat_1('#skF_6',A_332)
      | ~ r2_hidden(A_333,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_66,c_1539])).

tff(c_56,plain,(
    k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5','#skF_7')) != k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_2086,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ v5_relat_1('#skF_6','#skF_2')
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2080,c_56])).

tff(c_2092,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_2086])).

tff(c_2094,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2092])).

tff(c_2102,plain,
    ( ~ m1_subset_1('#skF_7','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_2094])).

tff(c_2105,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2102])).

tff(c_2107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_2105])).

tff(c_2108,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2092])).

tff(c_2252,plain,(
    ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1808,c_2108])).

tff(c_2256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2252])).

tff(c_2257,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1359])).

tff(c_2280,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2257,c_8])).

tff(c_2283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2280])).

tff(c_2285,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_3617,plain,(
    ! [B_528,A_529,C_530] :
      ( k1_xboole_0 = B_528
      | k1_relset_1(A_529,B_528,C_530) = A_529
      | ~ v1_funct_2(C_530,A_529,B_528)
      | ~ m1_subset_1(C_530,k1_zfmisc_1(k2_zfmisc_1(A_529,B_528))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3635,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_3617])).

tff(c_3644,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_196,c_3635])).

tff(c_3645,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3644])).

tff(c_303,plain,(
    ! [B_119,A_120] :
      ( r2_hidden(k1_funct_1(B_119,A_120),k2_relat_1(B_119))
      | ~ r2_hidden(A_120,k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ r2_hidden(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_310,plain,(
    ! [B_119,A_120] :
      ( m1_subset_1(k1_funct_1(B_119,A_120),k2_relat_1(B_119))
      | v1_xboole_0(k2_relat_1(B_119))
      | ~ r2_hidden(A_120,k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(resolution,[status(thm)],[c_303,c_12])).

tff(c_2284,plain,(
    ! [B_113] :
      ( r2_hidden(B_113,k1_relat_1('#skF_6'))
      | ~ m1_subset_1(B_113,k2_relat_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_3719,plain,(
    ! [A_543,B_544,C_545] :
      ( k7_partfun1(A_543,B_544,C_545) = k1_funct_1(B_544,C_545)
      | ~ r2_hidden(C_545,k1_relat_1(B_544))
      | ~ v1_funct_1(B_544)
      | ~ v5_relat_1(B_544,A_543)
      | ~ v1_relat_1(B_544) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3731,plain,(
    ! [A_543,B_113] :
      ( k7_partfun1(A_543,'#skF_6',B_113) = k1_funct_1('#skF_6',B_113)
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_543)
      | ~ v1_relat_1('#skF_6')
      | ~ m1_subset_1(B_113,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2284,c_3719])).

tff(c_3829,plain,(
    ! [A_557,B_558] :
      ( k7_partfun1(A_557,'#skF_6',B_558) = k1_funct_1('#skF_6',B_558)
      | ~ v5_relat_1('#skF_6',A_557)
      | ~ m1_subset_1(B_558,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_66,c_3731])).

tff(c_3833,plain,(
    ! [B_559] :
      ( k7_partfun1('#skF_2','#skF_6',B_559) = k1_funct_1('#skF_6',B_559)
      | ~ m1_subset_1(B_559,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_167,c_3829])).

tff(c_3837,plain,(
    ! [A_120] :
      ( k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5',A_120)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',A_120))
      | v1_xboole_0(k2_relat_1('#skF_5'))
      | ~ r2_hidden(A_120,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_310,c_3833])).

tff(c_3852,plain,(
    ! [A_120] :
      ( k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5',A_120)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',A_120))
      | v1_xboole_0(k2_relat_1('#skF_5'))
      | ~ r2_hidden(A_120,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_72,c_3645,c_3837])).

tff(c_3870,plain,(
    ! [A_561] :
      ( k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5',A_561)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',A_561))
      | ~ r2_hidden(A_561,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2285,c_3852])).

tff(c_3876,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3870,c_56])).

tff(c_3882,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3876])).

tff(c_3886,plain,
    ( ~ m1_subset_1('#skF_7','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_3882])).

tff(c_3889,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3886])).

tff(c_3891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_3889])).

tff(c_3892,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3876])).

tff(c_3958,plain,(
    ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3952,c_3892])).

tff(c_3975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3958])).

tff(c_3976,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3644])).

tff(c_3990,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3976,c_8])).

tff(c_3993,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3990])).

tff(c_3995,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_4005,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3995,c_79])).

tff(c_4011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4005])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:20:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.78/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.13  
% 5.78/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.13  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.78/2.13  
% 5.78/2.13  %Foreground sorts:
% 5.78/2.13  
% 5.78/2.13  
% 5.78/2.13  %Background operators:
% 5.78/2.13  
% 5.78/2.13  
% 5.78/2.13  %Foreground operators:
% 5.78/2.13  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.78/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.78/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.78/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.78/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.78/2.13  tff('#skF_7', type, '#skF_7': $i).
% 5.78/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.78/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.78/2.13  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 5.78/2.13  tff('#skF_5', type, '#skF_5': $i).
% 5.78/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.78/2.13  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 5.78/2.13  tff('#skF_6', type, '#skF_6': $i).
% 5.78/2.13  tff('#skF_2', type, '#skF_2': $i).
% 5.78/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.78/2.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.78/2.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.78/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.78/2.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.78/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.78/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.78/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.78/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.78/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.78/2.13  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.78/2.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.78/2.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.78/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.78/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.78/2.13  
% 6.12/2.16  tff(f_183, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 6.12/2.16  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.12/2.16  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.12/2.16  tff(f_158, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 6.12/2.16  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.12/2.16  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.12/2.16  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.12/2.16  tff(f_41, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 6.12/2.16  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.12/2.16  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.12/2.16  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.12/2.16  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.12/2.16  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 6.12/2.16  tff(f_134, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 6.12/2.16  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.16  tff(c_74, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.16  tff(c_62, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.16  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.16  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.16  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.16  tff(c_210, plain, (![A_104, B_105, C_106]: (k2_relset_1(A_104, B_105, C_106)=k2_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.12/2.16  tff(c_223, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_210])).
% 6.12/2.16  tff(c_183, plain, (![A_94, B_95, C_96]: (k1_relset_1(A_94, B_95, C_96)=k1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.12/2.16  tff(c_195, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_183])).
% 6.12/2.16  tff(c_60, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.16  tff(c_197, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_60])).
% 6.12/2.16  tff(c_228, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_197])).
% 6.12/2.16  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.16  tff(c_70, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.16  tff(c_3754, plain, (![C_551, B_548, A_547, F_549, D_550, E_546]: (k1_funct_1(k8_funct_2(B_548, C_551, A_547, D_550, E_546), F_549)=k1_funct_1(E_546, k1_funct_1(D_550, F_549)) | k1_xboole_0=B_548 | ~r1_tarski(k2_relset_1(B_548, C_551, D_550), k1_relset_1(C_551, A_547, E_546)) | ~m1_subset_1(F_549, B_548) | ~m1_subset_1(E_546, k1_zfmisc_1(k2_zfmisc_1(C_551, A_547))) | ~v1_funct_1(E_546) | ~m1_subset_1(D_550, k1_zfmisc_1(k2_zfmisc_1(B_548, C_551))) | ~v1_funct_2(D_550, B_548, C_551) | ~v1_funct_1(D_550) | v1_xboole_0(C_551))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.12/2.16  tff(c_3758, plain, (![A_547, E_546, F_549]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_547, '#skF_5', E_546), F_549)=k1_funct_1(E_546, k1_funct_1('#skF_5', F_549)) | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', A_547, E_546)) | ~m1_subset_1(F_549, '#skF_3') | ~m1_subset_1(E_546, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_547))) | ~v1_funct_1(E_546) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_223, c_3754])).
% 6.12/2.16  tff(c_3767, plain, (![A_547, E_546, F_549]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_547, '#skF_5', E_546), F_549)=k1_funct_1(E_546, k1_funct_1('#skF_5', F_549)) | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', A_547, E_546)) | ~m1_subset_1(F_549, '#skF_3') | ~m1_subset_1(E_546, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_547))) | ~v1_funct_1(E_546) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_3758])).
% 6.12/2.16  tff(c_3924, plain, (![A_566, E_567, F_568]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_566, '#skF_5', E_567), F_568)=k1_funct_1(E_567, k1_funct_1('#skF_5', F_568)) | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', A_566, E_567)) | ~m1_subset_1(F_568, '#skF_3') | ~m1_subset_1(E_567, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_566))) | ~v1_funct_1(E_567))), inference(negUnitSimplification, [status(thm)], [c_74, c_58, c_3767])).
% 6.12/2.16  tff(c_3926, plain, (![F_568]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_568)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_568)) | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6')) | ~m1_subset_1(F_568, '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_3924])).
% 6.12/2.16  tff(c_3952, plain, (![F_576]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_576)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_576)) | ~m1_subset_1(F_576, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_228, c_3926])).
% 6.12/2.16  tff(c_86, plain, (![B_70, A_71]: (v1_xboole_0(B_70) | ~m1_subset_1(B_70, A_71) | ~v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.12/2.16  tff(c_98, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_86])).
% 6.12/2.16  tff(c_99, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_98])).
% 6.12/2.16  tff(c_14, plain, (![B_9, A_8]: (r2_hidden(B_9, A_8) | ~m1_subset_1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.12/2.16  tff(c_148, plain, (![C_85, B_86, A_87]: (r2_hidden(C_85, B_86) | ~r2_hidden(C_85, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.12/2.16  tff(c_283, plain, (![B_113, B_114, A_115]: (r2_hidden(B_113, B_114) | ~r1_tarski(A_115, B_114) | ~m1_subset_1(B_113, A_115) | v1_xboole_0(A_115))), inference(resolution, [status(thm)], [c_14, c_148])).
% 6.12/2.16  tff(c_288, plain, (![B_113]: (r2_hidden(B_113, k1_relat_1('#skF_6')) | ~m1_subset_1(B_113, k2_relat_1('#skF_5')) | v1_xboole_0(k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_228, c_283])).
% 6.12/2.16  tff(c_311, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_288])).
% 6.12/2.16  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.12/2.16  tff(c_76, plain, (![B_67, A_68]: (~v1_xboole_0(B_67) | B_67=A_68 | ~v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.12/2.16  tff(c_79, plain, (![A_68]: (k1_xboole_0=A_68 | ~v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_8, c_76])).
% 6.12/2.16  tff(c_317, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_311, c_79])).
% 6.12/2.16  tff(c_320, plain, (r1_tarski(k1_xboole_0, k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_228])).
% 6.12/2.16  tff(c_321, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_317, c_223])).
% 6.12/2.16  tff(c_1760, plain, (![C_296, B_293, D_295, E_291, F_294, A_292]: (k1_funct_1(k8_funct_2(B_293, C_296, A_292, D_295, E_291), F_294)=k1_funct_1(E_291, k1_funct_1(D_295, F_294)) | k1_xboole_0=B_293 | ~r1_tarski(k2_relset_1(B_293, C_296, D_295), k1_relset_1(C_296, A_292, E_291)) | ~m1_subset_1(F_294, B_293) | ~m1_subset_1(E_291, k1_zfmisc_1(k2_zfmisc_1(C_296, A_292))) | ~v1_funct_1(E_291) | ~m1_subset_1(D_295, k1_zfmisc_1(k2_zfmisc_1(B_293, C_296))) | ~v1_funct_2(D_295, B_293, C_296) | ~v1_funct_1(D_295) | v1_xboole_0(C_296))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.12/2.16  tff(c_1764, plain, (![A_292, E_291, F_294]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_292, '#skF_5', E_291), F_294)=k1_funct_1(E_291, k1_funct_1('#skF_5', F_294)) | k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, k1_relset_1('#skF_4', A_292, E_291)) | ~m1_subset_1(F_294, '#skF_3') | ~m1_subset_1(E_291, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_292))) | ~v1_funct_1(E_291) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_321, c_1760])).
% 6.12/2.16  tff(c_1773, plain, (![A_292, E_291, F_294]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_292, '#skF_5', E_291), F_294)=k1_funct_1(E_291, k1_funct_1('#skF_5', F_294)) | k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, k1_relset_1('#skF_4', A_292, E_291)) | ~m1_subset_1(F_294, '#skF_3') | ~m1_subset_1(E_291, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_292))) | ~v1_funct_1(E_291) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1764])).
% 6.12/2.16  tff(c_1787, plain, (![A_301, E_302, F_303]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_301, '#skF_5', E_302), F_303)=k1_funct_1(E_302, k1_funct_1('#skF_5', F_303)) | ~r1_tarski(k1_xboole_0, k1_relset_1('#skF_4', A_301, E_302)) | ~m1_subset_1(F_303, '#skF_3') | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_301))) | ~v1_funct_1(E_302))), inference(negUnitSimplification, [status(thm)], [c_74, c_58, c_1773])).
% 6.12/2.16  tff(c_1801, plain, (![F_303]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_303)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_303)) | ~r1_tarski(k1_xboole_0, k1_relset_1('#skF_4', '#skF_2', '#skF_6')) | ~m1_subset_1(F_303, '#skF_3') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_64, c_1787])).
% 6.12/2.16  tff(c_1808, plain, (![F_303]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_303)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_303)) | ~m1_subset_1(F_303, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_320, c_195, c_1801])).
% 6.12/2.16  tff(c_155, plain, (![C_88, B_89, A_90]: (v5_relat_1(C_88, B_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.12/2.16  tff(c_167, plain, (v5_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_155])).
% 6.12/2.16  tff(c_22, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.12/2.16  tff(c_107, plain, (![B_74, A_75]: (v1_relat_1(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.12/2.16  tff(c_114, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_107])).
% 6.12/2.16  tff(c_121, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_114])).
% 6.12/2.16  tff(c_126, plain, (![A_78, B_79]: (r2_hidden('#skF_1'(A_78, B_79), A_78) | r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.12/2.16  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.12/2.16  tff(c_131, plain, (![A_78]: (r1_tarski(A_78, A_78))), inference(resolution, [status(thm)], [c_126, c_4])).
% 6.12/2.16  tff(c_196, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_183])).
% 6.12/2.16  tff(c_1333, plain, (![B_240, A_241, C_242]: (k1_xboole_0=B_240 | k1_relset_1(A_241, B_240, C_242)=A_241 | ~v1_funct_2(C_242, A_241, B_240) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_241, B_240))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.12/2.16  tff(c_1351, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_1333])).
% 6.12/2.16  tff(c_1359, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_196, c_1351])).
% 6.12/2.16  tff(c_1360, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1359])).
% 6.12/2.16  tff(c_117, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_107])).
% 6.12/2.16  tff(c_124, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_117])).
% 6.12/2.16  tff(c_24, plain, (![B_16, A_15]: (r2_hidden(k1_funct_1(B_16, A_15), k2_relat_1(B_16)) | ~r2_hidden(A_15, k1_relat_1(B_16)) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.12/2.16  tff(c_326, plain, (![A_15]: (r2_hidden(k1_funct_1('#skF_5', A_15), k1_xboole_0) | ~r2_hidden(A_15, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_317, c_24])).
% 6.12/2.16  tff(c_341, plain, (![A_121]: (r2_hidden(k1_funct_1('#skF_5', A_121), k1_xboole_0) | ~r2_hidden(A_121, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_72, c_326])).
% 6.12/2.16  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.12/2.16  tff(c_347, plain, (![A_121, B_2]: (r2_hidden(k1_funct_1('#skF_5', A_121), B_2) | ~r1_tarski(k1_xboole_0, B_2) | ~r2_hidden(A_121, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_341, c_2])).
% 6.12/2.16  tff(c_1383, plain, (![A_244, B_245]: (r2_hidden(k1_funct_1('#skF_5', A_244), B_245) | ~r1_tarski(k1_xboole_0, B_245) | ~r2_hidden(A_244, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_347])).
% 6.12/2.16  tff(c_1515, plain, (![A_258, B_259, B_260]: (r2_hidden(k1_funct_1('#skF_5', A_258), B_259) | ~r1_tarski(B_260, B_259) | ~r1_tarski(k1_xboole_0, B_260) | ~r2_hidden(A_258, '#skF_3'))), inference(resolution, [status(thm)], [c_1383, c_2])).
% 6.12/2.16  tff(c_1519, plain, (![A_258]: (r2_hidden(k1_funct_1('#skF_5', A_258), k1_relat_1('#skF_6')) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~r2_hidden(A_258, '#skF_3'))), inference(resolution, [status(thm)], [c_320, c_1515])).
% 6.12/2.16  tff(c_1525, plain, (![A_258]: (r2_hidden(k1_funct_1('#skF_5', A_258), k1_relat_1('#skF_6')) | ~r2_hidden(A_258, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_1519])).
% 6.12/2.16  tff(c_1537, plain, (![A_262, B_263, C_264]: (k7_partfun1(A_262, B_263, C_264)=k1_funct_1(B_263, C_264) | ~r2_hidden(C_264, k1_relat_1(B_263)) | ~v1_funct_1(B_263) | ~v5_relat_1(B_263, A_262) | ~v1_relat_1(B_263))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.12/2.16  tff(c_1539, plain, (![A_262, A_258]: (k7_partfun1(A_262, '#skF_6', k1_funct_1('#skF_5', A_258))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', A_258)) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_262) | ~v1_relat_1('#skF_6') | ~r2_hidden(A_258, '#skF_3'))), inference(resolution, [status(thm)], [c_1525, c_1537])).
% 6.12/2.16  tff(c_2080, plain, (![A_332, A_333]: (k7_partfun1(A_332, '#skF_6', k1_funct_1('#skF_5', A_333))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', A_333)) | ~v5_relat_1('#skF_6', A_332) | ~r2_hidden(A_333, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_66, c_1539])).
% 6.12/2.16  tff(c_56, plain, (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', '#skF_7'))!=k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.16  tff(c_2086, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~v5_relat_1('#skF_6', '#skF_2') | ~r2_hidden('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2080, c_56])).
% 6.12/2.16  tff(c_2092, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~r2_hidden('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_2086])).
% 6.12/2.16  tff(c_2094, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_2092])).
% 6.12/2.16  tff(c_2102, plain, (~m1_subset_1('#skF_7', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_14, c_2094])).
% 6.12/2.16  tff(c_2105, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2102])).
% 6.12/2.16  tff(c_2107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_2105])).
% 6.12/2.16  tff(c_2108, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_2092])).
% 6.12/2.16  tff(c_2252, plain, (~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1808, c_2108])).
% 6.12/2.16  tff(c_2256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_2252])).
% 6.12/2.16  tff(c_2257, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1359])).
% 6.12/2.16  tff(c_2280, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2257, c_8])).
% 6.12/2.16  tff(c_2283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_2280])).
% 6.12/2.16  tff(c_2285, plain, (~v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_288])).
% 6.12/2.16  tff(c_3617, plain, (![B_528, A_529, C_530]: (k1_xboole_0=B_528 | k1_relset_1(A_529, B_528, C_530)=A_529 | ~v1_funct_2(C_530, A_529, B_528) | ~m1_subset_1(C_530, k1_zfmisc_1(k2_zfmisc_1(A_529, B_528))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.12/2.16  tff(c_3635, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_3617])).
% 6.12/2.16  tff(c_3644, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_196, c_3635])).
% 6.12/2.16  tff(c_3645, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_3644])).
% 6.12/2.16  tff(c_303, plain, (![B_119, A_120]: (r2_hidden(k1_funct_1(B_119, A_120), k2_relat_1(B_119)) | ~r2_hidden(A_120, k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.12/2.16  tff(c_12, plain, (![B_9, A_8]: (m1_subset_1(B_9, A_8) | ~r2_hidden(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.12/2.16  tff(c_310, plain, (![B_119, A_120]: (m1_subset_1(k1_funct_1(B_119, A_120), k2_relat_1(B_119)) | v1_xboole_0(k2_relat_1(B_119)) | ~r2_hidden(A_120, k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119))), inference(resolution, [status(thm)], [c_303, c_12])).
% 6.12/2.16  tff(c_2284, plain, (![B_113]: (r2_hidden(B_113, k1_relat_1('#skF_6')) | ~m1_subset_1(B_113, k2_relat_1('#skF_5')))), inference(splitRight, [status(thm)], [c_288])).
% 6.12/2.16  tff(c_3719, plain, (![A_543, B_544, C_545]: (k7_partfun1(A_543, B_544, C_545)=k1_funct_1(B_544, C_545) | ~r2_hidden(C_545, k1_relat_1(B_544)) | ~v1_funct_1(B_544) | ~v5_relat_1(B_544, A_543) | ~v1_relat_1(B_544))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.12/2.16  tff(c_3731, plain, (![A_543, B_113]: (k7_partfun1(A_543, '#skF_6', B_113)=k1_funct_1('#skF_6', B_113) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_543) | ~v1_relat_1('#skF_6') | ~m1_subset_1(B_113, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_2284, c_3719])).
% 6.12/2.16  tff(c_3829, plain, (![A_557, B_558]: (k7_partfun1(A_557, '#skF_6', B_558)=k1_funct_1('#skF_6', B_558) | ~v5_relat_1('#skF_6', A_557) | ~m1_subset_1(B_558, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_66, c_3731])).
% 6.12/2.16  tff(c_3833, plain, (![B_559]: (k7_partfun1('#skF_2', '#skF_6', B_559)=k1_funct_1('#skF_6', B_559) | ~m1_subset_1(B_559, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_167, c_3829])).
% 6.12/2.16  tff(c_3837, plain, (![A_120]: (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', A_120))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', A_120)) | v1_xboole_0(k2_relat_1('#skF_5')) | ~r2_hidden(A_120, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_310, c_3833])).
% 6.12/2.16  tff(c_3852, plain, (![A_120]: (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', A_120))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', A_120)) | v1_xboole_0(k2_relat_1('#skF_5')) | ~r2_hidden(A_120, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_72, c_3645, c_3837])).
% 6.12/2.16  tff(c_3870, plain, (![A_561]: (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', A_561))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', A_561)) | ~r2_hidden(A_561, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2285, c_3852])).
% 6.12/2.16  tff(c_3876, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~r2_hidden('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3870, c_56])).
% 6.12/2.16  tff(c_3882, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_3876])).
% 6.12/2.16  tff(c_3886, plain, (~m1_subset_1('#skF_7', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_14, c_3882])).
% 6.12/2.16  tff(c_3889, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3886])).
% 6.12/2.16  tff(c_3891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_3889])).
% 6.12/2.16  tff(c_3892, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_3876])).
% 6.12/2.16  tff(c_3958, plain, (~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3952, c_3892])).
% 6.12/2.16  tff(c_3975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_3958])).
% 6.12/2.16  tff(c_3976, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3644])).
% 6.12/2.16  tff(c_3990, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3976, c_8])).
% 6.12/2.16  tff(c_3993, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_3990])).
% 6.12/2.16  tff(c_3995, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_98])).
% 6.12/2.16  tff(c_4005, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3995, c_79])).
% 6.12/2.16  tff(c_4011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_4005])).
% 6.12/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.12/2.16  
% 6.12/2.16  Inference rules
% 6.12/2.16  ----------------------
% 6.12/2.16  #Ref     : 0
% 6.12/2.16  #Sup     : 778
% 6.12/2.16  #Fact    : 0
% 6.12/2.16  #Define  : 0
% 6.12/2.16  #Split   : 37
% 6.12/2.16  #Chain   : 0
% 6.12/2.16  #Close   : 0
% 6.12/2.16  
% 6.12/2.16  Ordering : KBO
% 6.12/2.16  
% 6.12/2.16  Simplification rules
% 6.12/2.16  ----------------------
% 6.12/2.16  #Subsume      : 126
% 6.12/2.16  #Demod        : 456
% 6.12/2.16  #Tautology    : 169
% 6.12/2.16  #SimpNegUnit  : 121
% 6.12/2.16  #BackRed      : 107
% 6.12/2.16  
% 6.12/2.16  #Partial instantiations: 0
% 6.12/2.16  #Strategies tried      : 1
% 6.12/2.16  
% 6.12/2.16  Timing (in seconds)
% 6.12/2.16  ----------------------
% 6.12/2.16  Preprocessing        : 0.36
% 6.12/2.16  Parsing              : 0.19
% 6.12/2.16  CNF conversion       : 0.03
% 6.12/2.16  Main loop            : 1.02
% 6.12/2.16  Inferencing          : 0.35
% 6.12/2.16  Reduction            : 0.31
% 6.12/2.16  Demodulation         : 0.20
% 6.12/2.16  BG Simplification    : 0.04
% 6.12/2.16  Subsumption          : 0.23
% 6.12/2.16  Abstraction          : 0.05
% 6.12/2.16  MUC search           : 0.00
% 6.12/2.16  Cooper               : 0.00
% 6.12/2.16  Total                : 1.42
% 6.12/2.16  Index Insertion      : 0.00
% 6.12/2.16  Index Deletion       : 0.00
% 6.12/2.16  Index Matching       : 0.00
% 6.12/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
