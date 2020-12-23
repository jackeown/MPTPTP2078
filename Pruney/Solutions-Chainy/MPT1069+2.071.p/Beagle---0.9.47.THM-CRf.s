%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:55 EST 2020

% Result     : Theorem 4.94s
% Output     : CNFRefutation 4.94s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 384 expanded)
%              Number of leaves         :   44 ( 152 expanded)
%              Depth                    :   15
%              Number of atoms          :  249 (1319 expanded)
%              Number of equality atoms :   51 ( 282 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_121,axiom,(
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

tff(f_72,axiom,(
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

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_145,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_82,plain,(
    ! [C_72,B_73,A_74] :
      ( v5_relat_1(C_72,B_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_89,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_82])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_72,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_69])).

tff(c_78,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_72])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_48,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_124,plain,(
    ! [A_86,B_87,C_88] :
      ( k2_relset_1(A_86,B_87,C_88) = k2_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_132,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_124])).

tff(c_100,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_107,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_100])).

tff(c_46,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_109,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_46])).

tff(c_137,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_109])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_995,plain,(
    ! [F_190,B_185,A_187,C_188,E_186,D_189] :
      ( k1_funct_1(k8_funct_2(B_185,C_188,A_187,D_189,E_186),F_190) = k1_funct_1(E_186,k1_funct_1(D_189,F_190))
      | k1_xboole_0 = B_185
      | ~ r1_tarski(k2_relset_1(B_185,C_188,D_189),k1_relset_1(C_188,A_187,E_186))
      | ~ m1_subset_1(F_190,B_185)
      | ~ m1_subset_1(E_186,k1_zfmisc_1(k2_zfmisc_1(C_188,A_187)))
      | ~ v1_funct_1(E_186)
      | ~ m1_subset_1(D_189,k1_zfmisc_1(k2_zfmisc_1(B_185,C_188)))
      | ~ v1_funct_2(D_189,B_185,C_188)
      | ~ v1_funct_1(D_189)
      | v1_xboole_0(C_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1003,plain,(
    ! [A_187,E_186,F_190] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_187,'#skF_4',E_186),F_190) = k1_funct_1(E_186,k1_funct_1('#skF_4',F_190))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_187,E_186))
      | ~ m1_subset_1(F_190,'#skF_2')
      | ~ m1_subset_1(E_186,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_187)))
      | ~ v1_funct_1(E_186)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_995])).

tff(c_1016,plain,(
    ! [A_187,E_186,F_190] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_187,'#skF_4',E_186),F_190) = k1_funct_1(E_186,k1_funct_1('#skF_4',F_190))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_187,E_186))
      | ~ m1_subset_1(F_190,'#skF_2')
      | ~ m1_subset_1(E_186,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_187)))
      | ~ v1_funct_1(E_186)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1003])).

tff(c_1040,plain,(
    ! [A_194,E_195,F_196] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_194,'#skF_4',E_195),F_196) = k1_funct_1(E_195,k1_funct_1('#skF_4',F_196))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_194,E_195))
      | ~ m1_subset_1(F_196,'#skF_2')
      | ~ m1_subset_1(E_195,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_194)))
      | ~ v1_funct_1(E_195) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_44,c_1016])).

tff(c_1042,plain,(
    ! [F_196] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_196) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_196))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_196,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_1040])).

tff(c_1044,plain,(
    ! [F_196] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_196) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_196))
      | ~ m1_subset_1(F_196,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_137,c_1042])).

tff(c_20,plain,(
    ! [A_13,B_16] :
      ( k1_funct_1(A_13,B_16) = k1_xboole_0
      | r2_hidden(B_16,k1_relat_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_922,plain,(
    ! [A_172,B_173,C_174] :
      ( k7_partfun1(A_172,B_173,C_174) = k1_funct_1(B_173,C_174)
      | ~ r2_hidden(C_174,k1_relat_1(B_173))
      | ~ v1_funct_1(B_173)
      | ~ v5_relat_1(B_173,A_172)
      | ~ v1_relat_1(B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1060,plain,(
    ! [A_198,A_199,B_200] :
      ( k7_partfun1(A_198,A_199,B_200) = k1_funct_1(A_199,B_200)
      | ~ v5_relat_1(A_199,A_198)
      | k1_funct_1(A_199,B_200) = k1_xboole_0
      | ~ v1_funct_1(A_199)
      | ~ v1_relat_1(A_199) ) ),
    inference(resolution,[status(thm)],[c_20,c_922])).

tff(c_1066,plain,(
    ! [B_200] :
      ( k7_partfun1('#skF_1','#skF_5',B_200) = k1_funct_1('#skF_5',B_200)
      | k1_funct_1('#skF_5',B_200) = k1_xboole_0
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_89,c_1060])).

tff(c_1106,plain,(
    ! [B_205] :
      ( k7_partfun1('#skF_1','#skF_5',B_205) = k1_funct_1('#skF_5',B_205)
      | k1_funct_1('#skF_5',B_205) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_52,c_1066])).

tff(c_42,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1112,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1106,c_42])).

tff(c_1670,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1112])).

tff(c_1827,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1044,c_1670])).

tff(c_1831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1827])).

tff(c_1832,plain,(
    k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1112])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_75,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_69])).

tff(c_81,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_75])).

tff(c_143,plain,(
    ! [B_91,A_92] :
      ( m1_subset_1(B_91,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_91),A_92)))
      | ~ r1_tarski(k2_relat_1(B_91),A_92)
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_22,plain,(
    ! [C_20,B_19,A_18] :
      ( v5_relat_1(C_20,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_171,plain,(
    ! [B_95,A_96] :
      ( v5_relat_1(B_95,A_96)
      | ~ r1_tarski(k2_relat_1(B_95),A_96)
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_143,c_22])).

tff(c_174,plain,
    ( v5_relat_1('#skF_4',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_137,c_171])).

tff(c_177,plain,(
    v5_relat_1('#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_58,c_174])).

tff(c_943,plain,(
    ! [D_177,C_178,A_179,B_180] :
      ( r2_hidden(k1_funct_1(D_177,C_178),k2_relset_1(A_179,B_180,D_177))
      | k1_xboole_0 = B_180
      | ~ r2_hidden(C_178,A_179)
      | ~ m1_subset_1(D_177,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ v1_funct_2(D_177,A_179,B_180)
      | ~ v1_funct_1(D_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_952,plain,(
    ! [C_178] :
      ( r2_hidden(k1_funct_1('#skF_4',C_178),k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_178,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_943])).

tff(c_958,plain,(
    ! [C_178] :
      ( r2_hidden(k1_funct_1('#skF_4',C_178),k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_178,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_952])).

tff(c_959,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_958])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_967,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_2])).

tff(c_970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_967])).

tff(c_974,plain,(
    ! [C_182] :
      ( r2_hidden(k1_funct_1('#skF_4',C_182),k2_relat_1('#skF_4'))
      | ~ r2_hidden(C_182,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_958])).

tff(c_12,plain,(
    ! [C_12,A_9,B_10] :
      ( r2_hidden(C_12,A_9)
      | ~ r2_hidden(C_12,k2_relat_1(B_10))
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_976,plain,(
    ! [C_182,A_9] :
      ( r2_hidden(k1_funct_1('#skF_4',C_182),A_9)
      | ~ v5_relat_1('#skF_4',A_9)
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(C_182,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_974,c_12])).

tff(c_979,plain,(
    ! [C_182,A_9] :
      ( r2_hidden(k1_funct_1('#skF_4',C_182),A_9)
      | ~ v5_relat_1('#skF_4',A_9)
      | ~ r2_hidden(C_182,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_976])).

tff(c_16,plain,(
    ! [B_16,A_13] :
      ( r2_hidden(k4_tarski(B_16,k1_funct_1(A_13,B_16)),A_13)
      | ~ r2_hidden(B_16,k1_relat_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1854,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_4','#skF_6'),k1_xboole_0),'#skF_5')
    | ~ r2_hidden(k1_funct_1('#skF_4','#skF_6'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1832,c_16])).

tff(c_1860,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_4','#skF_6'),k1_xboole_0),'#skF_5')
    | ~ r2_hidden(k1_funct_1('#skF_4','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_52,c_1854])).

tff(c_2029,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1860])).

tff(c_2032,plain,
    ( ~ v5_relat_1('#skF_4',k1_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_979,c_2029])).

tff(c_2044,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_2032])).

tff(c_2052,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_2044])).

tff(c_2055,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2052])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2059,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2055,c_4])).

tff(c_2063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2059])).

tff(c_2065,plain,(
    r2_hidden(k1_funct_1('#skF_4','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1860])).

tff(c_30,plain,(
    ! [A_27,B_28,C_30] :
      ( k7_partfun1(A_27,B_28,C_30) = k1_funct_1(B_28,C_30)
      | ~ r2_hidden(C_30,k1_relat_1(B_28))
      | ~ v1_funct_1(B_28)
      | ~ v5_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2069,plain,(
    ! [A_27] :
      ( k7_partfun1(A_27,'#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_27)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2065,c_30])).

tff(c_2084,plain,(
    ! [A_292] :
      ( k7_partfun1(A_292,'#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_xboole_0
      | ~ v5_relat_1('#skF_5',A_292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_52,c_1832,c_2069])).

tff(c_1833,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1112])).

tff(c_1955,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1832,c_1833])).

tff(c_1956,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1955,c_42])).

tff(c_2090,plain,(
    ~ v5_relat_1('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2084,c_1956])).

tff(c_2106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_2090])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:56:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.94/2.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/2.01  
% 4.94/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/2.01  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.94/2.01  
% 4.94/2.01  %Foreground sorts:
% 4.94/2.01  
% 4.94/2.01  
% 4.94/2.01  %Background operators:
% 4.94/2.01  
% 4.94/2.01  
% 4.94/2.01  %Foreground operators:
% 4.94/2.01  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.94/2.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.94/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.94/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.94/2.01  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.94/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.94/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.94/2.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.94/2.01  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.94/2.01  tff('#skF_5', type, '#skF_5': $i).
% 4.94/2.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.94/2.01  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.94/2.01  tff('#skF_6', type, '#skF_6': $i).
% 4.94/2.01  tff('#skF_2', type, '#skF_2': $i).
% 4.94/2.01  tff('#skF_3', type, '#skF_3': $i).
% 4.94/2.01  tff('#skF_1', type, '#skF_1': $i).
% 4.94/2.01  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.94/2.01  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.94/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.94/2.01  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.94/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.94/2.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.94/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.94/2.01  tff('#skF_4', type, '#skF_4': $i).
% 4.94/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.94/2.01  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.94/2.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.94/2.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.94/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.94/2.01  
% 4.94/2.03  tff(f_170, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 4.94/2.03  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.94/2.03  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.94/2.03  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.94/2.03  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.94/2.03  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.94/2.03  tff(f_121, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 4.94/2.03  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 4.94/2.03  tff(f_97, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 4.94/2.03  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.94/2.03  tff(f_133, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.94/2.03  tff(f_145, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 4.94/2.03  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.94/2.03  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 4.94/2.03  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.94/2.03  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.94/2.03  tff(c_82, plain, (![C_72, B_73, A_74]: (v5_relat_1(C_72, B_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.94/2.03  tff(c_89, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_82])).
% 4.94/2.03  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.94/2.03  tff(c_69, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.94/2.03  tff(c_72, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_69])).
% 4.94/2.03  tff(c_78, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_72])).
% 4.94/2.03  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.94/2.03  tff(c_48, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.94/2.03  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.94/2.03  tff(c_124, plain, (![A_86, B_87, C_88]: (k2_relset_1(A_86, B_87, C_88)=k2_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.94/2.03  tff(c_132, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_124])).
% 4.94/2.03  tff(c_100, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.94/2.03  tff(c_107, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_100])).
% 4.94/2.03  tff(c_46, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.94/2.03  tff(c_109, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_46])).
% 4.94/2.03  tff(c_137, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_109])).
% 4.94/2.03  tff(c_60, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.94/2.03  tff(c_44, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.94/2.03  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.94/2.03  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.94/2.03  tff(c_995, plain, (![F_190, B_185, A_187, C_188, E_186, D_189]: (k1_funct_1(k8_funct_2(B_185, C_188, A_187, D_189, E_186), F_190)=k1_funct_1(E_186, k1_funct_1(D_189, F_190)) | k1_xboole_0=B_185 | ~r1_tarski(k2_relset_1(B_185, C_188, D_189), k1_relset_1(C_188, A_187, E_186)) | ~m1_subset_1(F_190, B_185) | ~m1_subset_1(E_186, k1_zfmisc_1(k2_zfmisc_1(C_188, A_187))) | ~v1_funct_1(E_186) | ~m1_subset_1(D_189, k1_zfmisc_1(k2_zfmisc_1(B_185, C_188))) | ~v1_funct_2(D_189, B_185, C_188) | ~v1_funct_1(D_189) | v1_xboole_0(C_188))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.94/2.03  tff(c_1003, plain, (![A_187, E_186, F_190]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_187, '#skF_4', E_186), F_190)=k1_funct_1(E_186, k1_funct_1('#skF_4', F_190)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_187, E_186)) | ~m1_subset_1(F_190, '#skF_2') | ~m1_subset_1(E_186, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_187))) | ~v1_funct_1(E_186) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_995])).
% 4.94/2.03  tff(c_1016, plain, (![A_187, E_186, F_190]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_187, '#skF_4', E_186), F_190)=k1_funct_1(E_186, k1_funct_1('#skF_4', F_190)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_187, E_186)) | ~m1_subset_1(F_190, '#skF_2') | ~m1_subset_1(E_186, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_187))) | ~v1_funct_1(E_186) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1003])).
% 4.94/2.03  tff(c_1040, plain, (![A_194, E_195, F_196]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_194, '#skF_4', E_195), F_196)=k1_funct_1(E_195, k1_funct_1('#skF_4', F_196)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_194, E_195)) | ~m1_subset_1(F_196, '#skF_2') | ~m1_subset_1(E_195, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_194))) | ~v1_funct_1(E_195))), inference(negUnitSimplification, [status(thm)], [c_60, c_44, c_1016])).
% 4.94/2.03  tff(c_1042, plain, (![F_196]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_196)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_196)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~m1_subset_1(F_196, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_1040])).
% 4.94/2.03  tff(c_1044, plain, (![F_196]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_196)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_196)) | ~m1_subset_1(F_196, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_137, c_1042])).
% 4.94/2.03  tff(c_20, plain, (![A_13, B_16]: (k1_funct_1(A_13, B_16)=k1_xboole_0 | r2_hidden(B_16, k1_relat_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.94/2.03  tff(c_922, plain, (![A_172, B_173, C_174]: (k7_partfun1(A_172, B_173, C_174)=k1_funct_1(B_173, C_174) | ~r2_hidden(C_174, k1_relat_1(B_173)) | ~v1_funct_1(B_173) | ~v5_relat_1(B_173, A_172) | ~v1_relat_1(B_173))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.94/2.03  tff(c_1060, plain, (![A_198, A_199, B_200]: (k7_partfun1(A_198, A_199, B_200)=k1_funct_1(A_199, B_200) | ~v5_relat_1(A_199, A_198) | k1_funct_1(A_199, B_200)=k1_xboole_0 | ~v1_funct_1(A_199) | ~v1_relat_1(A_199))), inference(resolution, [status(thm)], [c_20, c_922])).
% 4.94/2.03  tff(c_1066, plain, (![B_200]: (k7_partfun1('#skF_1', '#skF_5', B_200)=k1_funct_1('#skF_5', B_200) | k1_funct_1('#skF_5', B_200)=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_89, c_1060])).
% 4.94/2.03  tff(c_1106, plain, (![B_205]: (k7_partfun1('#skF_1', '#skF_5', B_205)=k1_funct_1('#skF_5', B_205) | k1_funct_1('#skF_5', B_205)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_52, c_1066])).
% 4.94/2.03  tff(c_42, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.94/2.03  tff(c_1112, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1106, c_42])).
% 4.94/2.03  tff(c_1670, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_1112])).
% 4.94/2.03  tff(c_1827, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1044, c_1670])).
% 4.94/2.03  tff(c_1831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1827])).
% 4.94/2.03  tff(c_1832, plain, (k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1112])).
% 4.94/2.03  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.94/2.03  tff(c_75, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_69])).
% 4.94/2.03  tff(c_81, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_75])).
% 4.94/2.03  tff(c_143, plain, (![B_91, A_92]: (m1_subset_1(B_91, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_91), A_92))) | ~r1_tarski(k2_relat_1(B_91), A_92) | ~v1_funct_1(B_91) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.94/2.03  tff(c_22, plain, (![C_20, B_19, A_18]: (v5_relat_1(C_20, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.94/2.03  tff(c_171, plain, (![B_95, A_96]: (v5_relat_1(B_95, A_96) | ~r1_tarski(k2_relat_1(B_95), A_96) | ~v1_funct_1(B_95) | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_143, c_22])).
% 4.94/2.03  tff(c_174, plain, (v5_relat_1('#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_137, c_171])).
% 4.94/2.03  tff(c_177, plain, (v5_relat_1('#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_58, c_174])).
% 4.94/2.03  tff(c_943, plain, (![D_177, C_178, A_179, B_180]: (r2_hidden(k1_funct_1(D_177, C_178), k2_relset_1(A_179, B_180, D_177)) | k1_xboole_0=B_180 | ~r2_hidden(C_178, A_179) | ~m1_subset_1(D_177, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~v1_funct_2(D_177, A_179, B_180) | ~v1_funct_1(D_177))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.94/2.03  tff(c_952, plain, (![C_178]: (r2_hidden(k1_funct_1('#skF_4', C_178), k2_relat_1('#skF_4')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_178, '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_943])).
% 4.94/2.03  tff(c_958, plain, (![C_178]: (r2_hidden(k1_funct_1('#skF_4', C_178), k2_relat_1('#skF_4')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_178, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_952])).
% 4.94/2.03  tff(c_959, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_958])).
% 4.94/2.03  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.94/2.03  tff(c_967, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_959, c_2])).
% 4.94/2.03  tff(c_970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_967])).
% 4.94/2.03  tff(c_974, plain, (![C_182]: (r2_hidden(k1_funct_1('#skF_4', C_182), k2_relat_1('#skF_4')) | ~r2_hidden(C_182, '#skF_2'))), inference(splitRight, [status(thm)], [c_958])).
% 4.94/2.03  tff(c_12, plain, (![C_12, A_9, B_10]: (r2_hidden(C_12, A_9) | ~r2_hidden(C_12, k2_relat_1(B_10)) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.94/2.03  tff(c_976, plain, (![C_182, A_9]: (r2_hidden(k1_funct_1('#skF_4', C_182), A_9) | ~v5_relat_1('#skF_4', A_9) | ~v1_relat_1('#skF_4') | ~r2_hidden(C_182, '#skF_2'))), inference(resolution, [status(thm)], [c_974, c_12])).
% 4.94/2.03  tff(c_979, plain, (![C_182, A_9]: (r2_hidden(k1_funct_1('#skF_4', C_182), A_9) | ~v5_relat_1('#skF_4', A_9) | ~r2_hidden(C_182, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_976])).
% 4.94/2.03  tff(c_16, plain, (![B_16, A_13]: (r2_hidden(k4_tarski(B_16, k1_funct_1(A_13, B_16)), A_13) | ~r2_hidden(B_16, k1_relat_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.94/2.03  tff(c_1854, plain, (r2_hidden(k4_tarski(k1_funct_1('#skF_4', '#skF_6'), k1_xboole_0), '#skF_5') | ~r2_hidden(k1_funct_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1832, c_16])).
% 4.94/2.03  tff(c_1860, plain, (r2_hidden(k4_tarski(k1_funct_1('#skF_4', '#skF_6'), k1_xboole_0), '#skF_5') | ~r2_hidden(k1_funct_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_52, c_1854])).
% 4.94/2.03  tff(c_2029, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1860])).
% 4.94/2.03  tff(c_2032, plain, (~v5_relat_1('#skF_4', k1_relat_1('#skF_5')) | ~r2_hidden('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_979, c_2029])).
% 4.94/2.03  tff(c_2044, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_2032])).
% 4.94/2.03  tff(c_2052, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_2044])).
% 4.94/2.03  tff(c_2055, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2052])).
% 4.94/2.03  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.94/2.03  tff(c_2059, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2055, c_4])).
% 4.94/2.03  tff(c_2063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2059])).
% 4.94/2.03  tff(c_2065, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_1860])).
% 4.94/2.03  tff(c_30, plain, (![A_27, B_28, C_30]: (k7_partfun1(A_27, B_28, C_30)=k1_funct_1(B_28, C_30) | ~r2_hidden(C_30, k1_relat_1(B_28)) | ~v1_funct_1(B_28) | ~v5_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.94/2.03  tff(c_2069, plain, (![A_27]: (k7_partfun1(A_27, '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_27) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_2065, c_30])).
% 4.94/2.03  tff(c_2084, plain, (![A_292]: (k7_partfun1(A_292, '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_xboole_0 | ~v5_relat_1('#skF_5', A_292))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_52, c_1832, c_2069])).
% 4.94/2.03  tff(c_1833, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_1112])).
% 4.94/2.03  tff(c_1955, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1832, c_1833])).
% 4.94/2.03  tff(c_1956, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1955, c_42])).
% 4.94/2.03  tff(c_2090, plain, (~v5_relat_1('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2084, c_1956])).
% 4.94/2.03  tff(c_2106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_2090])).
% 4.94/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/2.03  
% 4.94/2.03  Inference rules
% 4.94/2.03  ----------------------
% 4.94/2.03  #Ref     : 0
% 4.94/2.03  #Sup     : 435
% 4.94/2.03  #Fact    : 0
% 4.94/2.03  #Define  : 0
% 4.94/2.03  #Split   : 22
% 4.94/2.03  #Chain   : 0
% 4.94/2.03  #Close   : 0
% 4.94/2.03  
% 4.94/2.03  Ordering : KBO
% 4.94/2.03  
% 4.94/2.03  Simplification rules
% 4.94/2.03  ----------------------
% 4.94/2.03  #Subsume      : 34
% 4.94/2.03  #Demod        : 465
% 4.94/2.03  #Tautology    : 159
% 4.94/2.03  #SimpNegUnit  : 20
% 4.94/2.03  #BackRed      : 78
% 4.94/2.03  
% 4.94/2.03  #Partial instantiations: 0
% 4.94/2.03  #Strategies tried      : 1
% 4.94/2.03  
% 4.94/2.03  Timing (in seconds)
% 4.94/2.03  ----------------------
% 4.94/2.03  Preprocessing        : 0.43
% 4.94/2.03  Parsing              : 0.21
% 4.94/2.04  CNF conversion       : 0.04
% 4.94/2.04  Main loop            : 0.73
% 4.94/2.04  Inferencing          : 0.25
% 4.94/2.04  Reduction            : 0.25
% 4.94/2.04  Demodulation         : 0.17
% 4.94/2.04  BG Simplification    : 0.04
% 4.94/2.04  Subsumption          : 0.13
% 4.94/2.04  Abstraction          : 0.04
% 4.94/2.04  MUC search           : 0.00
% 4.94/2.04  Cooper               : 0.00
% 4.94/2.04  Total                : 1.21
% 4.94/2.04  Index Insertion      : 0.00
% 4.94/2.04  Index Deletion       : 0.00
% 4.94/2.04  Index Matching       : 0.00
% 4.94/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
