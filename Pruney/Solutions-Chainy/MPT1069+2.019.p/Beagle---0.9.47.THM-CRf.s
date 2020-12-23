%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:47 EST 2020

% Result     : Theorem 6.69s
% Output     : CNFRefutation 7.09s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 729 expanded)
%              Number of leaves         :   49 ( 270 expanded)
%              Depth                    :   19
%              Number of atoms          :  363 (2746 expanded)
%              Number of equality atoms :   61 ( 510 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_206,negated_conjecture,(
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

tff(f_122,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_157,axiom,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_181,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_169,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_770,plain,(
    ! [C_173,A_174,B_175] :
      ( ~ v1_xboole_0(C_173)
      | ~ v1_funct_2(C_173,A_174,B_175)
      | ~ v1_funct_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | v1_xboole_0(B_175)
      | v1_xboole_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_789,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_770])).

tff(c_811,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_789])).

tff(c_812,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_811])).

tff(c_815,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_812])).

tff(c_70,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_390,plain,(
    ! [A_129,B_130,C_131] :
      ( k1_relset_1(A_129,B_130,C_131) = k1_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_408,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_390])).

tff(c_293,plain,(
    ! [A_116,B_117,C_118] :
      ( k2_relset_1(A_116,B_117,C_118) = k2_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_312,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_293])).

tff(c_68,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_317,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_68])).

tff(c_419,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_317])).

tff(c_74,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_973,plain,(
    ! [A_195,D_196,E_194,C_198,B_193,F_197] :
      ( k1_funct_1(k8_funct_2(B_193,C_198,A_195,D_196,E_194),F_197) = k1_funct_1(E_194,k1_funct_1(D_196,F_197))
      | k1_xboole_0 = B_193
      | ~ r1_tarski(k2_relset_1(B_193,C_198,D_196),k1_relset_1(C_198,A_195,E_194))
      | ~ m1_subset_1(F_197,B_193)
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(C_198,A_195)))
      | ~ v1_funct_1(E_194)
      | ~ m1_subset_1(D_196,k1_zfmisc_1(k2_zfmisc_1(B_193,C_198)))
      | ~ v1_funct_2(D_196,B_193,C_198)
      | ~ v1_funct_1(D_196)
      | v1_xboole_0(C_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_997,plain,(
    ! [B_193,D_196,F_197] :
      ( k1_funct_1(k8_funct_2(B_193,'#skF_3','#skF_1',D_196,'#skF_5'),F_197) = k1_funct_1('#skF_5',k1_funct_1(D_196,F_197))
      | k1_xboole_0 = B_193
      | ~ r1_tarski(k2_relset_1(B_193,'#skF_3',D_196),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_197,B_193)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_196,k1_zfmisc_1(k2_zfmisc_1(B_193,'#skF_3')))
      | ~ v1_funct_2(D_196,B_193,'#skF_3')
      | ~ v1_funct_1(D_196)
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_973])).

tff(c_1025,plain,(
    ! [B_193,D_196,F_197] :
      ( k1_funct_1(k8_funct_2(B_193,'#skF_3','#skF_1',D_196,'#skF_5'),F_197) = k1_funct_1('#skF_5',k1_funct_1(D_196,F_197))
      | k1_xboole_0 = B_193
      | ~ r1_tarski(k2_relset_1(B_193,'#skF_3',D_196),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_197,B_193)
      | ~ m1_subset_1(D_196,k1_zfmisc_1(k2_zfmisc_1(B_193,'#skF_3')))
      | ~ v1_funct_2(D_196,B_193,'#skF_3')
      | ~ v1_funct_1(D_196)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_997])).

tff(c_1207,plain,(
    ! [B_219,D_220,F_221] :
      ( k1_funct_1(k8_funct_2(B_219,'#skF_3','#skF_1',D_220,'#skF_5'),F_221) = k1_funct_1('#skF_5',k1_funct_1(D_220,F_221))
      | k1_xboole_0 = B_219
      | ~ r1_tarski(k2_relset_1(B_219,'#skF_3',D_220),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_221,B_219)
      | ~ m1_subset_1(D_220,k1_zfmisc_1(k2_zfmisc_1(B_219,'#skF_3')))
      | ~ v1_funct_2(D_220,B_219,'#skF_3')
      | ~ v1_funct_1(D_220) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1025])).

tff(c_1215,plain,(
    ! [F_221] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_221) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_221))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_221,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_1207])).

tff(c_1217,plain,(
    ! [F_221] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_221) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_221))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_221,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_419,c_1215])).

tff(c_1218,plain,(
    ! [F_221] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_221) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_221))
      | ~ m1_subset_1(F_221,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1217])).

tff(c_261,plain,(
    ! [C_105,B_106,A_107] :
      ( v5_relat_1(C_105,B_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_279,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_261])).

tff(c_171,plain,(
    ! [C_90,A_91,B_92] :
      ( v1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_187,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_171])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_929,plain,(
    ! [D_183,C_184,B_185,A_186] :
      ( r2_hidden(k1_funct_1(D_183,C_184),B_185)
      | k1_xboole_0 = B_185
      | ~ r2_hidden(C_184,A_186)
      | ~ m1_subset_1(D_183,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185)))
      | ~ v1_funct_2(D_183,A_186,B_185)
      | ~ v1_funct_1(D_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_3354,plain,(
    ! [D_362,A_363,B_364,B_365] :
      ( r2_hidden(k1_funct_1(D_362,A_363),B_364)
      | k1_xboole_0 = B_364
      | ~ m1_subset_1(D_362,k1_zfmisc_1(k2_zfmisc_1(B_365,B_364)))
      | ~ v1_funct_2(D_362,B_365,B_364)
      | ~ v1_funct_1(D_362)
      | v1_xboole_0(B_365)
      | ~ m1_subset_1(A_363,B_365) ) ),
    inference(resolution,[status(thm)],[c_20,c_929])).

tff(c_3381,plain,(
    ! [A_363] :
      ( r2_hidden(k1_funct_1('#skF_4',A_363),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_363,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_76,c_3354])).

tff(c_3415,plain,(
    ! [A_363] :
      ( r2_hidden(k1_funct_1('#skF_4',A_363),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_363,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_3381])).

tff(c_3418,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3415])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3424,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3418,c_4])).

tff(c_3429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3424])).

tff(c_3431,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3415])).

tff(c_665,plain,(
    ! [C_167,A_168,B_169] :
      ( v1_partfun1(C_167,A_168)
      | ~ v1_funct_2(C_167,A_168,B_169)
      | ~ v1_funct_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | v1_xboole_0(B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_681,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_665])).

tff(c_700,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_681])).

tff(c_701,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_700])).

tff(c_599,plain,(
    ! [D_161,C_162,B_163,A_164] :
      ( m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(C_162,B_163)))
      | ~ r1_tarski(k2_relat_1(D_161),B_163)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(C_162,A_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_704,plain,(
    ! [B_170] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_170)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_170) ) ),
    inference(resolution,[status(thm)],[c_76,c_599])).

tff(c_38,plain,(
    ! [C_29,A_27,B_28] :
      ( v1_funct_2(C_29,A_27,B_28)
      | ~ v1_partfun1(C_29,A_27)
      | ~ v1_funct_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_712,plain,(
    ! [B_170] :
      ( v1_funct_2('#skF_4','#skF_2',B_170)
      | ~ v1_partfun1('#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_170) ) ),
    inference(resolution,[status(thm)],[c_704,c_38])).

tff(c_760,plain,(
    ! [B_172] :
      ( v1_funct_2('#skF_4','#skF_2',B_172)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_701,c_712])).

tff(c_768,plain,(
    v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_419,c_760])).

tff(c_616,plain,(
    ! [B_163] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_163)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_163) ) ),
    inference(resolution,[status(thm)],[c_76,c_599])).

tff(c_34,plain,(
    ! [A_20,B_21,C_22] :
      ( k2_relset_1(A_20,B_21,C_22) = k2_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_893,plain,(
    ! [B_181] :
      ( k2_relset_1('#skF_2',B_181,'#skF_4') = k2_relat_1('#skF_4')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_181) ) ),
    inference(resolution,[status(thm)],[c_704,c_34])).

tff(c_901,plain,(
    k2_relset_1('#skF_2',k1_relat_1('#skF_5'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_419,c_893])).

tff(c_985,plain,(
    ! [A_195,E_194,F_197] :
      ( k1_funct_1(k8_funct_2('#skF_2',k1_relat_1('#skF_5'),A_195,'#skF_4',E_194),F_197) = k1_funct_1(E_194,k1_funct_1('#skF_4',F_197))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1(k1_relat_1('#skF_5'),A_195,E_194))
      | ~ m1_subset_1(F_197,'#skF_2')
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),A_195)))
      | ~ v1_funct_1(E_194)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5'))))
      | ~ v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_973])).

tff(c_1015,plain,(
    ! [A_195,E_194,F_197] :
      ( k1_funct_1(k8_funct_2('#skF_2',k1_relat_1('#skF_5'),A_195,'#skF_4',E_194),F_197) = k1_funct_1(E_194,k1_funct_1('#skF_4',F_197))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1(k1_relat_1('#skF_5'),A_195,E_194))
      | ~ m1_subset_1(F_197,'#skF_2')
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),A_195)))
      | ~ v1_funct_1(E_194)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5'))))
      | v1_xboole_0(k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_768,c_985])).

tff(c_1016,plain,(
    ! [A_195,E_194,F_197] :
      ( k1_funct_1(k8_funct_2('#skF_2',k1_relat_1('#skF_5'),A_195,'#skF_4',E_194),F_197) = k1_funct_1(E_194,k1_funct_1('#skF_4',F_197))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1(k1_relat_1('#skF_5'),A_195,E_194))
      | ~ m1_subset_1(F_197,'#skF_2')
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),A_195)))
      | ~ v1_funct_1(E_194)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5'))))
      | v1_xboole_0(k1_relat_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1015])).

tff(c_1699,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_1016])).

tff(c_1705,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_616,c_1699])).

tff(c_1715,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_1705])).

tff(c_1717,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_1016])).

tff(c_3364,plain,(
    ! [A_363] :
      ( r2_hidden(k1_funct_1('#skF_4',A_363),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_363,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1717,c_3354])).

tff(c_3395,plain,(
    ! [A_363] :
      ( r2_hidden(k1_funct_1('#skF_4',A_363),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_363,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_768,c_3364])).

tff(c_3596,plain,(
    ! [A_363] :
      ( r2_hidden(k1_funct_1('#skF_4',A_363),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ m1_subset_1(A_363,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3431,c_3395])).

tff(c_3597,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3596])).

tff(c_16,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1233,plain,(
    ! [D_231,A_232,B_233] :
      ( m1_subset_1(D_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233)))
      | ~ r1_tarski(k2_relat_1(D_231),B_233)
      | ~ m1_subset_1(D_231,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_599])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1288,plain,(
    ! [D_235,A_236,B_237] :
      ( r1_tarski(D_235,k2_zfmisc_1(A_236,B_237))
      | ~ r1_tarski(k2_relat_1(D_235),B_237)
      | ~ m1_subset_1(D_235,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1233,c_22])).

tff(c_1294,plain,(
    ! [A_236] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_236,k1_relat_1('#skF_5')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_419,c_1288])).

tff(c_1296,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_1294])).

tff(c_188,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_171])).

tff(c_58,plain,(
    ! [B_60,A_59] :
      ( v1_funct_2(B_60,k1_relat_1(B_60),A_59)
      | ~ r1_tarski(k2_relat_1(B_60),A_59)
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_56,plain,(
    ! [B_60,A_59] :
      ( m1_subset_1(B_60,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_60),A_59)))
      | ~ r1_tarski(k2_relat_1(B_60),A_59)
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_2925,plain,(
    ! [B_326,A_327] :
      ( v1_partfun1(B_326,k1_relat_1(B_326))
      | ~ v1_funct_2(B_326,k1_relat_1(B_326),A_327)
      | v1_xboole_0(A_327)
      | ~ r1_tarski(k2_relat_1(B_326),A_327)
      | ~ v1_funct_1(B_326)
      | ~ v1_relat_1(B_326) ) ),
    inference(resolution,[status(thm)],[c_56,c_665])).

tff(c_2950,plain,(
    ! [B_328,A_329] :
      ( v1_partfun1(B_328,k1_relat_1(B_328))
      | v1_xboole_0(A_329)
      | ~ r1_tarski(k2_relat_1(B_328),A_329)
      | ~ v1_funct_1(B_328)
      | ~ v1_relat_1(B_328) ) ),
    inference(resolution,[status(thm)],[c_58,c_2925])).

tff(c_2961,plain,
    ( v1_partfun1('#skF_4',k1_relat_1('#skF_4'))
    | v1_xboole_0(k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_419,c_2950])).

tff(c_2970,plain,
    ( v1_partfun1('#skF_4',k1_relat_1('#skF_4'))
    | v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_80,c_2961])).

tff(c_2972,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2970])).

tff(c_2976,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2972,c_4])).

tff(c_2981,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2976,c_1717])).

tff(c_2995,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2981])).

tff(c_2997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1296,c_2995])).

tff(c_2999,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2970])).

tff(c_3603,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3597,c_2999])).

tff(c_3622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3603])).

tff(c_3625,plain,(
    ! [A_373] :
      ( r2_hidden(k1_funct_1('#skF_4',A_373),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_373,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_3596])).

tff(c_52,plain,(
    ! [A_38,B_39,C_41] :
      ( k7_partfun1(A_38,B_39,C_41) = k1_funct_1(B_39,C_41)
      | ~ r2_hidden(C_41,k1_relat_1(B_39))
      | ~ v1_funct_1(B_39)
      | ~ v5_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3629,plain,(
    ! [A_38,A_373] :
      ( k7_partfun1(A_38,'#skF_5',k1_funct_1('#skF_4',A_373)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_373))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_38)
      | ~ v1_relat_1('#skF_5')
      | ~ m1_subset_1(A_373,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3625,c_52])).

tff(c_4566,plain,(
    ! [A_430,A_431] :
      ( k7_partfun1(A_430,'#skF_5',k1_funct_1('#skF_4',A_431)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_431))
      | ~ v5_relat_1('#skF_5',A_430)
      | ~ m1_subset_1(A_431,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_74,c_3629])).

tff(c_64,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_4572,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v5_relat_1('#skF_5','#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4566,c_64])).

tff(c_4578,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_279,c_4572])).

tff(c_4582,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1218,c_4578])).

tff(c_4586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4582])).

tff(c_4588,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1294])).

tff(c_4625,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4588,c_22])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_139,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(B_87,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_153,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_139])).

tff(c_4743,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4625,c_153])).

tff(c_4786,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4743,c_2])).

tff(c_4793,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_815,c_4786])).

tff(c_4794,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_812])).

tff(c_4799,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_4794,c_4])).

tff(c_4803,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:02:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.69/2.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.69/2.41  
% 6.69/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.69/2.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.69/2.42  
% 6.69/2.42  %Foreground sorts:
% 6.69/2.42  
% 6.69/2.42  
% 6.69/2.42  %Background operators:
% 6.69/2.42  
% 6.69/2.42  
% 6.69/2.42  %Foreground operators:
% 6.69/2.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.69/2.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.69/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.69/2.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.69/2.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.69/2.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.69/2.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.69/2.42  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 6.69/2.42  tff('#skF_5', type, '#skF_5': $i).
% 6.69/2.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.69/2.42  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 6.69/2.42  tff('#skF_6', type, '#skF_6': $i).
% 6.69/2.42  tff('#skF_2', type, '#skF_2': $i).
% 6.69/2.42  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.69/2.42  tff('#skF_3', type, '#skF_3': $i).
% 6.69/2.42  tff('#skF_1', type, '#skF_1': $i).
% 6.69/2.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.69/2.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.69/2.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.69/2.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.69/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.69/2.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.69/2.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.69/2.42  tff('#skF_4', type, '#skF_4': $i).
% 6.69/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.69/2.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.69/2.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.69/2.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.69/2.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.69/2.42  
% 7.09/2.45  tff(f_206, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 7.09/2.45  tff(f_122, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 7.09/2.45  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.09/2.45  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.09/2.45  tff(f_157, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 7.09/2.45  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.09/2.45  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.09/2.45  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.09/2.45  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 7.09/2.45  tff(f_181, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 7.09/2.45  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.09/2.45  tff(f_102, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 7.09/2.45  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 7.09/2.45  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 7.09/2.45  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.09/2.45  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.09/2.45  tff(f_169, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 7.09/2.45  tff(f_133, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 7.09/2.45  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.09/2.45  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.09/2.45  tff(c_66, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.09/2.45  tff(c_82, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.09/2.45  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.09/2.45  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.09/2.45  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.09/2.45  tff(c_770, plain, (![C_173, A_174, B_175]: (~v1_xboole_0(C_173) | ~v1_funct_2(C_173, A_174, B_175) | ~v1_funct_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | v1_xboole_0(B_175) | v1_xboole_0(A_174))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.09/2.45  tff(c_789, plain, (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_770])).
% 7.09/2.45  tff(c_811, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_789])).
% 7.09/2.45  tff(c_812, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_82, c_811])).
% 7.09/2.45  tff(c_815, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_812])).
% 7.09/2.45  tff(c_70, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.09/2.45  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.09/2.45  tff(c_390, plain, (![A_129, B_130, C_131]: (k1_relset_1(A_129, B_130, C_131)=k1_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.09/2.45  tff(c_408, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_390])).
% 7.09/2.45  tff(c_293, plain, (![A_116, B_117, C_118]: (k2_relset_1(A_116, B_117, C_118)=k2_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.09/2.45  tff(c_312, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_293])).
% 7.09/2.45  tff(c_68, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.09/2.45  tff(c_317, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_68])).
% 7.09/2.45  tff(c_419, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_408, c_317])).
% 7.09/2.45  tff(c_74, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.09/2.45  tff(c_973, plain, (![A_195, D_196, E_194, C_198, B_193, F_197]: (k1_funct_1(k8_funct_2(B_193, C_198, A_195, D_196, E_194), F_197)=k1_funct_1(E_194, k1_funct_1(D_196, F_197)) | k1_xboole_0=B_193 | ~r1_tarski(k2_relset_1(B_193, C_198, D_196), k1_relset_1(C_198, A_195, E_194)) | ~m1_subset_1(F_197, B_193) | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(C_198, A_195))) | ~v1_funct_1(E_194) | ~m1_subset_1(D_196, k1_zfmisc_1(k2_zfmisc_1(B_193, C_198))) | ~v1_funct_2(D_196, B_193, C_198) | ~v1_funct_1(D_196) | v1_xboole_0(C_198))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.09/2.45  tff(c_997, plain, (![B_193, D_196, F_197]: (k1_funct_1(k8_funct_2(B_193, '#skF_3', '#skF_1', D_196, '#skF_5'), F_197)=k1_funct_1('#skF_5', k1_funct_1(D_196, F_197)) | k1_xboole_0=B_193 | ~r1_tarski(k2_relset_1(B_193, '#skF_3', D_196), k1_relat_1('#skF_5')) | ~m1_subset_1(F_197, B_193) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_196, k1_zfmisc_1(k2_zfmisc_1(B_193, '#skF_3'))) | ~v1_funct_2(D_196, B_193, '#skF_3') | ~v1_funct_1(D_196) | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_408, c_973])).
% 7.09/2.45  tff(c_1025, plain, (![B_193, D_196, F_197]: (k1_funct_1(k8_funct_2(B_193, '#skF_3', '#skF_1', D_196, '#skF_5'), F_197)=k1_funct_1('#skF_5', k1_funct_1(D_196, F_197)) | k1_xboole_0=B_193 | ~r1_tarski(k2_relset_1(B_193, '#skF_3', D_196), k1_relat_1('#skF_5')) | ~m1_subset_1(F_197, B_193) | ~m1_subset_1(D_196, k1_zfmisc_1(k2_zfmisc_1(B_193, '#skF_3'))) | ~v1_funct_2(D_196, B_193, '#skF_3') | ~v1_funct_1(D_196) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_997])).
% 7.09/2.45  tff(c_1207, plain, (![B_219, D_220, F_221]: (k1_funct_1(k8_funct_2(B_219, '#skF_3', '#skF_1', D_220, '#skF_5'), F_221)=k1_funct_1('#skF_5', k1_funct_1(D_220, F_221)) | k1_xboole_0=B_219 | ~r1_tarski(k2_relset_1(B_219, '#skF_3', D_220), k1_relat_1('#skF_5')) | ~m1_subset_1(F_221, B_219) | ~m1_subset_1(D_220, k1_zfmisc_1(k2_zfmisc_1(B_219, '#skF_3'))) | ~v1_funct_2(D_220, B_219, '#skF_3') | ~v1_funct_1(D_220))), inference(negUnitSimplification, [status(thm)], [c_82, c_1025])).
% 7.09/2.45  tff(c_1215, plain, (![F_221]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_221)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_221)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~m1_subset_1(F_221, '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_312, c_1207])).
% 7.09/2.45  tff(c_1217, plain, (![F_221]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_221)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_221)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_221, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_419, c_1215])).
% 7.09/2.45  tff(c_1218, plain, (![F_221]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_221)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_221)) | ~m1_subset_1(F_221, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_1217])).
% 7.09/2.45  tff(c_261, plain, (![C_105, B_106, A_107]: (v5_relat_1(C_105, B_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.09/2.45  tff(c_279, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_261])).
% 7.09/2.45  tff(c_171, plain, (![C_90, A_91, B_92]: (v1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.09/2.45  tff(c_187, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_171])).
% 7.09/2.45  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.09/2.45  tff(c_20, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.09/2.45  tff(c_929, plain, (![D_183, C_184, B_185, A_186]: (r2_hidden(k1_funct_1(D_183, C_184), B_185) | k1_xboole_0=B_185 | ~r2_hidden(C_184, A_186) | ~m1_subset_1(D_183, k1_zfmisc_1(k2_zfmisc_1(A_186, B_185))) | ~v1_funct_2(D_183, A_186, B_185) | ~v1_funct_1(D_183))), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.09/2.45  tff(c_3354, plain, (![D_362, A_363, B_364, B_365]: (r2_hidden(k1_funct_1(D_362, A_363), B_364) | k1_xboole_0=B_364 | ~m1_subset_1(D_362, k1_zfmisc_1(k2_zfmisc_1(B_365, B_364))) | ~v1_funct_2(D_362, B_365, B_364) | ~v1_funct_1(D_362) | v1_xboole_0(B_365) | ~m1_subset_1(A_363, B_365))), inference(resolution, [status(thm)], [c_20, c_929])).
% 7.09/2.45  tff(c_3381, plain, (![A_363]: (r2_hidden(k1_funct_1('#skF_4', A_363), '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_363, '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_3354])).
% 7.09/2.45  tff(c_3415, plain, (![A_363]: (r2_hidden(k1_funct_1('#skF_4', A_363), '#skF_3') | k1_xboole_0='#skF_3' | v1_xboole_0('#skF_2') | ~m1_subset_1(A_363, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_3381])).
% 7.09/2.45  tff(c_3418, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3415])).
% 7.09/2.45  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.09/2.45  tff(c_3424, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_3418, c_4])).
% 7.09/2.45  tff(c_3429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_3424])).
% 7.09/2.45  tff(c_3431, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_3415])).
% 7.09/2.45  tff(c_665, plain, (![C_167, A_168, B_169]: (v1_partfun1(C_167, A_168) | ~v1_funct_2(C_167, A_168, B_169) | ~v1_funct_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | v1_xboole_0(B_169))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.09/2.45  tff(c_681, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_665])).
% 7.09/2.45  tff(c_700, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_681])).
% 7.09/2.45  tff(c_701, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_82, c_700])).
% 7.09/2.45  tff(c_599, plain, (![D_161, C_162, B_163, A_164]: (m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(C_162, B_163))) | ~r1_tarski(k2_relat_1(D_161), B_163) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(C_162, A_164))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.09/2.45  tff(c_704, plain, (![B_170]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_170))) | ~r1_tarski(k2_relat_1('#skF_4'), B_170))), inference(resolution, [status(thm)], [c_76, c_599])).
% 7.09/2.45  tff(c_38, plain, (![C_29, A_27, B_28]: (v1_funct_2(C_29, A_27, B_28) | ~v1_partfun1(C_29, A_27) | ~v1_funct_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.09/2.45  tff(c_712, plain, (![B_170]: (v1_funct_2('#skF_4', '#skF_2', B_170) | ~v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), B_170))), inference(resolution, [status(thm)], [c_704, c_38])).
% 7.09/2.45  tff(c_760, plain, (![B_172]: (v1_funct_2('#skF_4', '#skF_2', B_172) | ~r1_tarski(k2_relat_1('#skF_4'), B_172))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_701, c_712])).
% 7.09/2.45  tff(c_768, plain, (v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_419, c_760])).
% 7.09/2.45  tff(c_616, plain, (![B_163]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_163))) | ~r1_tarski(k2_relat_1('#skF_4'), B_163))), inference(resolution, [status(thm)], [c_76, c_599])).
% 7.09/2.45  tff(c_34, plain, (![A_20, B_21, C_22]: (k2_relset_1(A_20, B_21, C_22)=k2_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.09/2.45  tff(c_893, plain, (![B_181]: (k2_relset_1('#skF_2', B_181, '#skF_4')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), B_181))), inference(resolution, [status(thm)], [c_704, c_34])).
% 7.09/2.45  tff(c_901, plain, (k2_relset_1('#skF_2', k1_relat_1('#skF_5'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_419, c_893])).
% 7.09/2.45  tff(c_985, plain, (![A_195, E_194, F_197]: (k1_funct_1(k8_funct_2('#skF_2', k1_relat_1('#skF_5'), A_195, '#skF_4', E_194), F_197)=k1_funct_1(E_194, k1_funct_1('#skF_4', F_197)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1(k1_relat_1('#skF_5'), A_195, E_194)) | ~m1_subset_1(F_197, '#skF_2') | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), A_195))) | ~v1_funct_1(E_194) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5')))) | ~v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_901, c_973])).
% 7.09/2.45  tff(c_1015, plain, (![A_195, E_194, F_197]: (k1_funct_1(k8_funct_2('#skF_2', k1_relat_1('#skF_5'), A_195, '#skF_4', E_194), F_197)=k1_funct_1(E_194, k1_funct_1('#skF_4', F_197)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1(k1_relat_1('#skF_5'), A_195, E_194)) | ~m1_subset_1(F_197, '#skF_2') | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), A_195))) | ~v1_funct_1(E_194) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5')))) | v1_xboole_0(k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_768, c_985])).
% 7.09/2.45  tff(c_1016, plain, (![A_195, E_194, F_197]: (k1_funct_1(k8_funct_2('#skF_2', k1_relat_1('#skF_5'), A_195, '#skF_4', E_194), F_197)=k1_funct_1(E_194, k1_funct_1('#skF_4', F_197)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1(k1_relat_1('#skF_5'), A_195, E_194)) | ~m1_subset_1(F_197, '#skF_2') | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), A_195))) | ~v1_funct_1(E_194) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5')))) | v1_xboole_0(k1_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1015])).
% 7.09/2.45  tff(c_1699, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5'))))), inference(splitLeft, [status(thm)], [c_1016])).
% 7.09/2.45  tff(c_1705, plain, (~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_616, c_1699])).
% 7.09/2.45  tff(c_1715, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_419, c_1705])).
% 7.09/2.45  tff(c_1717, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5'))))), inference(splitRight, [status(thm)], [c_1016])).
% 7.09/2.45  tff(c_3364, plain, (![A_363]: (r2_hidden(k1_funct_1('#skF_4', A_363), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_363, '#skF_2'))), inference(resolution, [status(thm)], [c_1717, c_3354])).
% 7.09/2.45  tff(c_3395, plain, (![A_363]: (r2_hidden(k1_funct_1('#skF_4', A_363), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_2') | ~m1_subset_1(A_363, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_768, c_3364])).
% 7.09/2.45  tff(c_3596, plain, (![A_363]: (r2_hidden(k1_funct_1('#skF_4', A_363), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | ~m1_subset_1(A_363, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_3431, c_3395])).
% 7.09/2.45  tff(c_3597, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3596])).
% 7.09/2.45  tff(c_16, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.09/2.45  tff(c_1233, plain, (![D_231, A_232, B_233]: (m1_subset_1(D_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))) | ~r1_tarski(k2_relat_1(D_231), B_233) | ~m1_subset_1(D_231, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_599])).
% 7.09/2.45  tff(c_22, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.09/2.45  tff(c_1288, plain, (![D_235, A_236, B_237]: (r1_tarski(D_235, k2_zfmisc_1(A_236, B_237)) | ~r1_tarski(k2_relat_1(D_235), B_237) | ~m1_subset_1(D_235, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1233, c_22])).
% 7.09/2.45  tff(c_1294, plain, (![A_236]: (r1_tarski('#skF_4', k2_zfmisc_1(A_236, k1_relat_1('#skF_5'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_419, c_1288])).
% 7.09/2.45  tff(c_1296, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1294])).
% 7.09/2.45  tff(c_188, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_171])).
% 7.09/2.45  tff(c_58, plain, (![B_60, A_59]: (v1_funct_2(B_60, k1_relat_1(B_60), A_59) | ~r1_tarski(k2_relat_1(B_60), A_59) | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.09/2.45  tff(c_56, plain, (![B_60, A_59]: (m1_subset_1(B_60, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_60), A_59))) | ~r1_tarski(k2_relat_1(B_60), A_59) | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.09/2.45  tff(c_2925, plain, (![B_326, A_327]: (v1_partfun1(B_326, k1_relat_1(B_326)) | ~v1_funct_2(B_326, k1_relat_1(B_326), A_327) | v1_xboole_0(A_327) | ~r1_tarski(k2_relat_1(B_326), A_327) | ~v1_funct_1(B_326) | ~v1_relat_1(B_326))), inference(resolution, [status(thm)], [c_56, c_665])).
% 7.09/2.45  tff(c_2950, plain, (![B_328, A_329]: (v1_partfun1(B_328, k1_relat_1(B_328)) | v1_xboole_0(A_329) | ~r1_tarski(k2_relat_1(B_328), A_329) | ~v1_funct_1(B_328) | ~v1_relat_1(B_328))), inference(resolution, [status(thm)], [c_58, c_2925])).
% 7.09/2.45  tff(c_2961, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4')) | v1_xboole_0(k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_419, c_2950])).
% 7.09/2.45  tff(c_2970, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4')) | v1_xboole_0(k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_80, c_2961])).
% 7.09/2.45  tff(c_2972, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_2970])).
% 7.09/2.45  tff(c_2976, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2972, c_4])).
% 7.09/2.45  tff(c_2981, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2976, c_1717])).
% 7.09/2.45  tff(c_2995, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2981])).
% 7.09/2.45  tff(c_2997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1296, c_2995])).
% 7.09/2.45  tff(c_2999, plain, (~v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_2970])).
% 7.09/2.45  tff(c_3603, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3597, c_2999])).
% 7.09/2.45  tff(c_3622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_3603])).
% 7.09/2.45  tff(c_3625, plain, (![A_373]: (r2_hidden(k1_funct_1('#skF_4', A_373), k1_relat_1('#skF_5')) | ~m1_subset_1(A_373, '#skF_2'))), inference(splitRight, [status(thm)], [c_3596])).
% 7.09/2.45  tff(c_52, plain, (![A_38, B_39, C_41]: (k7_partfun1(A_38, B_39, C_41)=k1_funct_1(B_39, C_41) | ~r2_hidden(C_41, k1_relat_1(B_39)) | ~v1_funct_1(B_39) | ~v5_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.09/2.45  tff(c_3629, plain, (![A_38, A_373]: (k7_partfun1(A_38, '#skF_5', k1_funct_1('#skF_4', A_373))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_373)) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_38) | ~v1_relat_1('#skF_5') | ~m1_subset_1(A_373, '#skF_2'))), inference(resolution, [status(thm)], [c_3625, c_52])).
% 7.09/2.45  tff(c_4566, plain, (![A_430, A_431]: (k7_partfun1(A_430, '#skF_5', k1_funct_1('#skF_4', A_431))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_431)) | ~v5_relat_1('#skF_5', A_430) | ~m1_subset_1(A_431, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_74, c_3629])).
% 7.09/2.45  tff(c_64, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.09/2.45  tff(c_4572, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v5_relat_1('#skF_5', '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4566, c_64])).
% 7.09/2.45  tff(c_4578, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_279, c_4572])).
% 7.09/2.45  tff(c_4582, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1218, c_4578])).
% 7.09/2.45  tff(c_4586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_4582])).
% 7.09/2.45  tff(c_4588, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1294])).
% 7.09/2.45  tff(c_4625, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_4588, c_22])).
% 7.09/2.45  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.09/2.45  tff(c_139, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(B_87, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.09/2.45  tff(c_153, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_139])).
% 7.09/2.45  tff(c_4743, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4625, c_153])).
% 7.09/2.45  tff(c_4786, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4743, c_2])).
% 7.09/2.45  tff(c_4793, plain, $false, inference(negUnitSimplification, [status(thm)], [c_815, c_4786])).
% 7.09/2.45  tff(c_4794, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_812])).
% 7.09/2.45  tff(c_4799, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_4794, c_4])).
% 7.09/2.45  tff(c_4803, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_4799])).
% 7.09/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.09/2.45  
% 7.09/2.45  Inference rules
% 7.09/2.45  ----------------------
% 7.09/2.45  #Ref     : 0
% 7.09/2.45  #Sup     : 989
% 7.09/2.45  #Fact    : 0
% 7.09/2.45  #Define  : 0
% 7.09/2.45  #Split   : 31
% 7.09/2.45  #Chain   : 0
% 7.09/2.45  #Close   : 0
% 7.09/2.45  
% 7.09/2.45  Ordering : KBO
% 7.09/2.45  
% 7.09/2.45  Simplification rules
% 7.09/2.45  ----------------------
% 7.09/2.45  #Subsume      : 261
% 7.09/2.45  #Demod        : 834
% 7.09/2.45  #Tautology    : 298
% 7.09/2.45  #SimpNegUnit  : 60
% 7.09/2.45  #BackRed      : 211
% 7.09/2.45  
% 7.09/2.45  #Partial instantiations: 0
% 7.09/2.45  #Strategies tried      : 1
% 7.09/2.45  
% 7.09/2.45  Timing (in seconds)
% 7.09/2.45  ----------------------
% 7.09/2.45  Preprocessing        : 0.37
% 7.09/2.45  Parsing              : 0.20
% 7.09/2.45  CNF conversion       : 0.03
% 7.09/2.45  Main loop            : 1.28
% 7.09/2.45  Inferencing          : 0.39
% 7.09/2.45  Reduction            : 0.47
% 7.09/2.45  Demodulation         : 0.33
% 7.09/2.45  BG Simplification    : 0.05
% 7.09/2.45  Subsumption          : 0.29
% 7.09/2.45  Abstraction          : 0.06
% 7.09/2.45  MUC search           : 0.00
% 7.09/2.45  Cooper               : 0.00
% 7.09/2.45  Total                : 1.71
% 7.09/2.45  Index Insertion      : 0.00
% 7.09/2.45  Index Deletion       : 0.00
% 7.09/2.45  Index Matching       : 0.00
% 7.09/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
