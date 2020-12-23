%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:17 EST 2020

% Result     : Theorem 7.11s
% Output     : CNFRefutation 7.11s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 385 expanded)
%              Number of leaves         :   54 ( 155 expanded)
%              Depth                    :   15
%              Number of atoms          :  281 (1215 expanded)
%              Number of equality atoms :   46 ( 107 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_187,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_145,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_143,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_133,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_113,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_111,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_167,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_72,plain,
    ( ~ v2_funct_2('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_126,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( v1_xboole_0(k2_zfmisc_1(A_16,B_17))
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_82,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_171,plain,(
    ! [B_84,A_85] :
      ( v1_xboole_0(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85))
      | ~ v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_182,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_82,c_171])).

tff(c_184,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_188,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_184])).

tff(c_66,plain,(
    ! [A_55] : k6_relat_1(A_55) = k6_partfun1(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_44,plain,(
    ! [A_32] : v2_funct_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_88,plain,(
    ! [A_32] : v2_funct_1(k6_partfun1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_44])).

tff(c_86,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_1053,plain,(
    ! [C_171,F_174,D_176,A_175,B_173,E_172] :
      ( k1_partfun1(A_175,B_173,C_171,D_176,E_172,F_174) = k5_relat_1(E_172,F_174)
      | ~ m1_subset_1(F_174,k1_zfmisc_1(k2_zfmisc_1(C_171,D_176)))
      | ~ v1_funct_1(F_174)
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(A_175,B_173)))
      | ~ v1_funct_1(E_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1063,plain,(
    ! [A_175,B_173,E_172] :
      ( k1_partfun1(A_175,B_173,'#skF_4','#skF_3',E_172,'#skF_6') = k5_relat_1(E_172,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(A_175,B_173)))
      | ~ v1_funct_1(E_172) ) ),
    inference(resolution,[status(thm)],[c_76,c_1053])).

tff(c_2592,plain,(
    ! [A_247,B_248,E_249] :
      ( k1_partfun1(A_247,B_248,'#skF_4','#skF_3',E_249,'#skF_6') = k5_relat_1(E_249,'#skF_6')
      | ~ m1_subset_1(E_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248)))
      | ~ v1_funct_1(E_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1063])).

tff(c_2619,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_2592])).

tff(c_2633,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2619])).

tff(c_60,plain,(
    ! [E_47,F_48,D_46,C_45,A_43,B_44] :
      ( m1_subset_1(k1_partfun1(A_43,B_44,C_45,D_46,E_47,F_48),k1_zfmisc_1(k2_zfmisc_1(A_43,D_46)))
      | ~ m1_subset_1(F_48,k1_zfmisc_1(k2_zfmisc_1(C_45,D_46)))
      | ~ v1_funct_1(F_48)
      | ~ m1_subset_1(E_47,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_1(E_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2907,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2633,c_60])).

tff(c_2914,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_2907])).

tff(c_54,plain,(
    ! [A_40] : m1_subset_1(k6_relat_1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_87,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54])).

tff(c_74,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_688,plain,(
    ! [D_136,C_137,A_138,B_139] :
      ( D_136 = C_137
      | ~ r2_relset_1(A_138,B_139,C_137,D_136)
      | ~ m1_subset_1(D_136,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_698,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_74,c_688])).

tff(c_717,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_698])).

tff(c_3179,plain,(
    k5_relat_1('#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2914,c_2633,c_2633,c_717])).

tff(c_84,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_70,plain,(
    ! [E_61,D_59,A_56,B_57,C_58] :
      ( k1_xboole_0 = C_58
      | v2_funct_1(D_59)
      | ~ v2_funct_1(k1_partfun1(A_56,B_57,B_57,C_58,D_59,E_61))
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1(B_57,C_58)))
      | ~ v1_funct_2(E_61,B_57,C_58)
      | ~ v1_funct_1(E_61)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_2(D_59,A_56,B_57)
      | ~ v1_funct_1(D_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2904,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k5_relat_1('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2633,c_70])).

tff(c_2911,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_2904])).

tff(c_2912,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_2911])).

tff(c_2916,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2912])).

tff(c_3185,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3179,c_2916])).

tff(c_3195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3185])).

tff(c_3196,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2912])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_135,plain,(
    ! [B_79,A_80] :
      ( ~ r1_xboole_0(B_79,A_80)
      | ~ r1_tarski(B_79,A_80)
      | v1_xboole_0(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_140,plain,(
    ! [A_81] :
      ( ~ r1_tarski(A_81,k1_xboole_0)
      | v1_xboole_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_20,c_135])).

tff(c_149,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_140])).

tff(c_3244,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3196,c_149])).

tff(c_3249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_3244])).

tff(c_3250,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_3257,plain,(
    ! [A_266,B_267] :
      ( r2_hidden('#skF_2'(A_266,B_267),A_266)
      | r1_tarski(A_266,B_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3261,plain,(
    ! [A_266,B_267] :
      ( ~ v1_xboole_0(A_266)
      | r1_tarski(A_266,B_267) ) ),
    inference(resolution,[status(thm)],[c_3257,c_2])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3282,plain,(
    ! [B_274,A_275] :
      ( B_274 = A_275
      | ~ r1_tarski(B_274,A_275)
      | ~ r1_tarski(A_275,B_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3295,plain,(
    ! [A_276] :
      ( k1_xboole_0 = A_276
      | ~ r1_tarski(A_276,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_3282])).

tff(c_3313,plain,(
    ! [A_277] :
      ( k1_xboole_0 = A_277
      | ~ v1_xboole_0(A_277) ) ),
    inference(resolution,[status(thm)],[c_3261,c_3295])).

tff(c_3331,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3250,c_3313])).

tff(c_3268,plain,(
    ! [A_270] :
      ( v1_xboole_0(k6_partfun1(A_270))
      | ~ v1_xboole_0(k2_zfmisc_1(A_270,A_270)) ) ),
    inference(resolution,[status(thm)],[c_87,c_171])).

tff(c_3273,plain,(
    ! [B_17] :
      ( v1_xboole_0(k6_partfun1(B_17))
      | ~ v1_xboole_0(B_17) ) ),
    inference(resolution,[status(thm)],[c_24,c_3268])).

tff(c_3329,plain,(
    ! [B_17] :
      ( k6_partfun1(B_17) = k1_xboole_0
      | ~ v1_xboole_0(B_17) ) ),
    inference(resolution,[status(thm)],[c_3273,c_3313])).

tff(c_3418,plain,(
    ! [B_283] :
      ( k6_partfun1(B_283) = '#skF_5'
      | ~ v1_xboole_0(B_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3331,c_3329])).

tff(c_3429,plain,(
    k6_partfun1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3250,c_3418])).

tff(c_3447,plain,(
    v2_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3429,c_88])).

tff(c_3454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_3447])).

tff(c_3455,plain,(
    ~ v2_funct_2('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_34,plain,(
    ! [A_26,B_27] : v1_relat_1(k2_zfmisc_1(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3559,plain,(
    ! [B_304,A_305] :
      ( v1_relat_1(B_304)
      | ~ m1_subset_1(B_304,k1_zfmisc_1(A_305))
      | ~ v1_relat_1(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3568,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_76,c_3559])).

tff(c_3577,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3568])).

tff(c_3798,plain,(
    ! [C_328,B_329,A_330] :
      ( v5_relat_1(C_328,B_329)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_330,B_329))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3813,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_3798])).

tff(c_3565,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_82,c_3559])).

tff(c_3574,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3565])).

tff(c_40,plain,(
    ! [A_31] : k2_relat_1(k6_relat_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_90,plain,(
    ! [A_31] : k2_relat_1(k6_partfun1(A_31)) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_40])).

tff(c_4643,plain,(
    ! [C_389,F_392,E_390,D_394,B_391,A_393] :
      ( k1_partfun1(A_393,B_391,C_389,D_394,E_390,F_392) = k5_relat_1(E_390,F_392)
      | ~ m1_subset_1(F_392,k1_zfmisc_1(k2_zfmisc_1(C_389,D_394)))
      | ~ v1_funct_1(F_392)
      | ~ m1_subset_1(E_390,k1_zfmisc_1(k2_zfmisc_1(A_393,B_391)))
      | ~ v1_funct_1(E_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4653,plain,(
    ! [A_393,B_391,E_390] :
      ( k1_partfun1(A_393,B_391,'#skF_4','#skF_3',E_390,'#skF_6') = k5_relat_1(E_390,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_390,k1_zfmisc_1(k2_zfmisc_1(A_393,B_391)))
      | ~ v1_funct_1(E_390) ) ),
    inference(resolution,[status(thm)],[c_76,c_4643])).

tff(c_6389,plain,(
    ! [A_471,B_472,E_473] :
      ( k1_partfun1(A_471,B_472,'#skF_4','#skF_3',E_473,'#skF_6') = k5_relat_1(E_473,'#skF_6')
      | ~ m1_subset_1(E_473,k1_zfmisc_1(k2_zfmisc_1(A_471,B_472)))
      | ~ v1_funct_1(E_473) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4653])).

tff(c_6416,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_6389])).

tff(c_6430,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_6416])).

tff(c_7001,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6430,c_60])).

tff(c_7007,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_7001])).

tff(c_4144,plain,(
    ! [D_355,C_356,A_357,B_358] :
      ( D_355 = C_356
      | ~ r2_relset_1(A_357,B_358,C_356,D_355)
      | ~ m1_subset_1(D_355,k1_zfmisc_1(k2_zfmisc_1(A_357,B_358)))
      | ~ m1_subset_1(C_356,k1_zfmisc_1(k2_zfmisc_1(A_357,B_358))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4154,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_74,c_4144])).

tff(c_4173,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_4154])).

tff(c_7099,plain,(
    k5_relat_1('#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7007,c_6430,c_6430,c_4173])).

tff(c_36,plain,(
    ! [A_28,B_30] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_28,B_30)),k2_relat_1(B_30))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_7118,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_3')),k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7099,c_36])).

tff(c_7124,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3574,c_3577,c_90,c_7118])).

tff(c_3696,plain,(
    ! [B_318,A_319] :
      ( r1_tarski(k2_relat_1(B_318),A_319)
      | ~ v5_relat_1(B_318,A_319)
      | ~ v1_relat_1(B_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3718,plain,(
    ! [B_318,A_319] :
      ( k2_relat_1(B_318) = A_319
      | ~ r1_tarski(A_319,k2_relat_1(B_318))
      | ~ v5_relat_1(B_318,A_319)
      | ~ v1_relat_1(B_318) ) ),
    inference(resolution,[status(thm)],[c_3696,c_12])).

tff(c_7128,plain,
    ( k2_relat_1('#skF_6') = '#skF_3'
    | ~ v5_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_7124,c_3718])).

tff(c_7141,plain,(
    k2_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3577,c_3813,c_7128])).

tff(c_3875,plain,(
    ! [B_333,A_334] :
      ( v5_relat_1(B_333,A_334)
      | ~ r1_tarski(k2_relat_1(B_333),A_334)
      | ~ v1_relat_1(B_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3899,plain,(
    ! [B_333] :
      ( v5_relat_1(B_333,k2_relat_1(B_333))
      | ~ v1_relat_1(B_333) ) ),
    inference(resolution,[status(thm)],[c_16,c_3875])).

tff(c_3921,plain,(
    ! [B_337] :
      ( v2_funct_2(B_337,k2_relat_1(B_337))
      | ~ v5_relat_1(B_337,k2_relat_1(B_337))
      | ~ v1_relat_1(B_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3935,plain,(
    ! [B_333] :
      ( v2_funct_2(B_333,k2_relat_1(B_333))
      | ~ v1_relat_1(B_333) ) ),
    inference(resolution,[status(thm)],[c_3899,c_3921])).

tff(c_7167,plain,
    ( v2_funct_2('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7141,c_3935])).

tff(c_7191,plain,(
    v2_funct_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3577,c_7167])).

tff(c_7193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3455,c_7191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:00:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.11/2.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.11/2.44  
% 7.11/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.11/2.45  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 7.11/2.45  
% 7.11/2.45  %Foreground sorts:
% 7.11/2.45  
% 7.11/2.45  
% 7.11/2.45  %Background operators:
% 7.11/2.45  
% 7.11/2.45  
% 7.11/2.45  %Foreground operators:
% 7.11/2.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.11/2.45  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.11/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.11/2.45  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.11/2.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.11/2.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.11/2.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.11/2.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.11/2.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.11/2.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.11/2.45  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.11/2.45  tff('#skF_5', type, '#skF_5': $i).
% 7.11/2.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.11/2.45  tff('#skF_6', type, '#skF_6': $i).
% 7.11/2.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.11/2.45  tff('#skF_3', type, '#skF_3': $i).
% 7.11/2.45  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.11/2.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.11/2.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.11/2.45  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.11/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.11/2.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.11/2.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.11/2.45  tff('#skF_4', type, '#skF_4': $i).
% 7.11/2.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.11/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.11/2.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.11/2.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.11/2.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.11/2.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.11/2.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.11/2.45  
% 7.11/2.47  tff(f_187, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.11/2.47  tff(f_60, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 7.11/2.47  tff(f_67, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 7.11/2.47  tff(f_145, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.11/2.47  tff(f_97, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.11/2.47  tff(f_143, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.11/2.47  tff(f_133, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.11/2.47  tff(f_113, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 7.11/2.47  tff(f_111, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.11/2.47  tff(f_167, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.11/2.47  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.11/2.47  tff(f_48, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.11/2.47  tff(f_56, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 7.11/2.47  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.11/2.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.11/2.47  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.11/2.47  tff(f_82, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.11/2.47  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.11/2.47  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.11/2.47  tff(f_93, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.11/2.47  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 7.11/2.47  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.11/2.47  tff(f_121, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.11/2.47  tff(c_72, plain, (~v2_funct_2('#skF_6', '#skF_3') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.11/2.47  tff(c_126, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_72])).
% 7.11/2.47  tff(c_24, plain, (![A_16, B_17]: (v1_xboole_0(k2_zfmisc_1(A_16, B_17)) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.11/2.47  tff(c_82, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.11/2.47  tff(c_171, plain, (![B_84, A_85]: (v1_xboole_0(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)) | ~v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.11/2.47  tff(c_182, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_171])).
% 7.11/2.47  tff(c_184, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_182])).
% 7.11/2.47  tff(c_188, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_184])).
% 7.11/2.47  tff(c_66, plain, (![A_55]: (k6_relat_1(A_55)=k6_partfun1(A_55))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.11/2.47  tff(c_44, plain, (![A_32]: (v2_funct_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.11/2.47  tff(c_88, plain, (![A_32]: (v2_funct_1(k6_partfun1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_44])).
% 7.11/2.47  tff(c_86, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.11/2.47  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.11/2.47  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.11/2.47  tff(c_1053, plain, (![C_171, F_174, D_176, A_175, B_173, E_172]: (k1_partfun1(A_175, B_173, C_171, D_176, E_172, F_174)=k5_relat_1(E_172, F_174) | ~m1_subset_1(F_174, k1_zfmisc_1(k2_zfmisc_1(C_171, D_176))) | ~v1_funct_1(F_174) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(A_175, B_173))) | ~v1_funct_1(E_172))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.11/2.47  tff(c_1063, plain, (![A_175, B_173, E_172]: (k1_partfun1(A_175, B_173, '#skF_4', '#skF_3', E_172, '#skF_6')=k5_relat_1(E_172, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(A_175, B_173))) | ~v1_funct_1(E_172))), inference(resolution, [status(thm)], [c_76, c_1053])).
% 7.11/2.47  tff(c_2592, plain, (![A_247, B_248, E_249]: (k1_partfun1(A_247, B_248, '#skF_4', '#skF_3', E_249, '#skF_6')=k5_relat_1(E_249, '#skF_6') | ~m1_subset_1(E_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))) | ~v1_funct_1(E_249))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1063])).
% 7.11/2.47  tff(c_2619, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_2592])).
% 7.11/2.47  tff(c_2633, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2619])).
% 7.11/2.47  tff(c_60, plain, (![E_47, F_48, D_46, C_45, A_43, B_44]: (m1_subset_1(k1_partfun1(A_43, B_44, C_45, D_46, E_47, F_48), k1_zfmisc_1(k2_zfmisc_1(A_43, D_46))) | ~m1_subset_1(F_48, k1_zfmisc_1(k2_zfmisc_1(C_45, D_46))) | ~v1_funct_1(F_48) | ~m1_subset_1(E_47, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_1(E_47))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.11/2.47  tff(c_2907, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2633, c_60])).
% 7.11/2.47  tff(c_2914, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_2907])).
% 7.11/2.47  tff(c_54, plain, (![A_40]: (m1_subset_1(k6_relat_1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.11/2.47  tff(c_87, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_54])).
% 7.11/2.47  tff(c_74, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.11/2.47  tff(c_688, plain, (![D_136, C_137, A_138, B_139]: (D_136=C_137 | ~r2_relset_1(A_138, B_139, C_137, D_136) | ~m1_subset_1(D_136, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.11/2.47  tff(c_698, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_74, c_688])).
% 7.11/2.47  tff(c_717, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_698])).
% 7.11/2.47  tff(c_3179, plain, (k5_relat_1('#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2914, c_2633, c_2633, c_717])).
% 7.11/2.47  tff(c_84, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.11/2.47  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.11/2.47  tff(c_70, plain, (![E_61, D_59, A_56, B_57, C_58]: (k1_xboole_0=C_58 | v2_funct_1(D_59) | ~v2_funct_1(k1_partfun1(A_56, B_57, B_57, C_58, D_59, E_61)) | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(B_57, C_58))) | ~v1_funct_2(E_61, B_57, C_58) | ~v1_funct_1(E_61) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_2(D_59, A_56, B_57) | ~v1_funct_1(D_59))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.11/2.47  tff(c_2904, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k5_relat_1('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2633, c_70])).
% 7.11/2.47  tff(c_2911, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k5_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_2904])).
% 7.11/2.47  tff(c_2912, plain, (k1_xboole_0='#skF_3' | ~v2_funct_1(k5_relat_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_126, c_2911])).
% 7.11/2.47  tff(c_2916, plain, (~v2_funct_1(k5_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_2912])).
% 7.11/2.47  tff(c_3185, plain, (~v2_funct_1(k6_partfun1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3179, c_2916])).
% 7.11/2.47  tff(c_3195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_3185])).
% 7.11/2.47  tff(c_3196, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2912])).
% 7.11/2.47  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.11/2.47  tff(c_20, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.11/2.47  tff(c_135, plain, (![B_79, A_80]: (~r1_xboole_0(B_79, A_80) | ~r1_tarski(B_79, A_80) | v1_xboole_0(B_79))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.11/2.47  tff(c_140, plain, (![A_81]: (~r1_tarski(A_81, k1_xboole_0) | v1_xboole_0(A_81))), inference(resolution, [status(thm)], [c_20, c_135])).
% 7.11/2.47  tff(c_149, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_140])).
% 7.11/2.47  tff(c_3244, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3196, c_149])).
% 7.11/2.47  tff(c_3249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_3244])).
% 7.11/2.47  tff(c_3250, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_182])).
% 7.11/2.47  tff(c_3257, plain, (![A_266, B_267]: (r2_hidden('#skF_2'(A_266, B_267), A_266) | r1_tarski(A_266, B_267))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.11/2.47  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.11/2.47  tff(c_3261, plain, (![A_266, B_267]: (~v1_xboole_0(A_266) | r1_tarski(A_266, B_267))), inference(resolution, [status(thm)], [c_3257, c_2])).
% 7.11/2.47  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.11/2.47  tff(c_3282, plain, (![B_274, A_275]: (B_274=A_275 | ~r1_tarski(B_274, A_275) | ~r1_tarski(A_275, B_274))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.11/2.47  tff(c_3295, plain, (![A_276]: (k1_xboole_0=A_276 | ~r1_tarski(A_276, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_3282])).
% 7.11/2.47  tff(c_3313, plain, (![A_277]: (k1_xboole_0=A_277 | ~v1_xboole_0(A_277))), inference(resolution, [status(thm)], [c_3261, c_3295])).
% 7.11/2.47  tff(c_3331, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3250, c_3313])).
% 7.11/2.47  tff(c_3268, plain, (![A_270]: (v1_xboole_0(k6_partfun1(A_270)) | ~v1_xboole_0(k2_zfmisc_1(A_270, A_270)))), inference(resolution, [status(thm)], [c_87, c_171])).
% 7.11/2.47  tff(c_3273, plain, (![B_17]: (v1_xboole_0(k6_partfun1(B_17)) | ~v1_xboole_0(B_17))), inference(resolution, [status(thm)], [c_24, c_3268])).
% 7.11/2.47  tff(c_3329, plain, (![B_17]: (k6_partfun1(B_17)=k1_xboole_0 | ~v1_xboole_0(B_17))), inference(resolution, [status(thm)], [c_3273, c_3313])).
% 7.11/2.47  tff(c_3418, plain, (![B_283]: (k6_partfun1(B_283)='#skF_5' | ~v1_xboole_0(B_283))), inference(demodulation, [status(thm), theory('equality')], [c_3331, c_3329])).
% 7.11/2.47  tff(c_3429, plain, (k6_partfun1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_3250, c_3418])).
% 7.11/2.47  tff(c_3447, plain, (v2_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3429, c_88])).
% 7.11/2.47  tff(c_3454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_3447])).
% 7.11/2.47  tff(c_3455, plain, (~v2_funct_2('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_72])).
% 7.11/2.47  tff(c_34, plain, (![A_26, B_27]: (v1_relat_1(k2_zfmisc_1(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.11/2.47  tff(c_3559, plain, (![B_304, A_305]: (v1_relat_1(B_304) | ~m1_subset_1(B_304, k1_zfmisc_1(A_305)) | ~v1_relat_1(A_305))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.11/2.47  tff(c_3568, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_76, c_3559])).
% 7.11/2.47  tff(c_3577, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3568])).
% 7.11/2.47  tff(c_3798, plain, (![C_328, B_329, A_330]: (v5_relat_1(C_328, B_329) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_330, B_329))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.11/2.47  tff(c_3813, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_3798])).
% 7.11/2.47  tff(c_3565, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_3559])).
% 7.11/2.47  tff(c_3574, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3565])).
% 7.11/2.47  tff(c_40, plain, (![A_31]: (k2_relat_1(k6_relat_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.11/2.47  tff(c_90, plain, (![A_31]: (k2_relat_1(k6_partfun1(A_31))=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_40])).
% 7.11/2.47  tff(c_4643, plain, (![C_389, F_392, E_390, D_394, B_391, A_393]: (k1_partfun1(A_393, B_391, C_389, D_394, E_390, F_392)=k5_relat_1(E_390, F_392) | ~m1_subset_1(F_392, k1_zfmisc_1(k2_zfmisc_1(C_389, D_394))) | ~v1_funct_1(F_392) | ~m1_subset_1(E_390, k1_zfmisc_1(k2_zfmisc_1(A_393, B_391))) | ~v1_funct_1(E_390))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.11/2.47  tff(c_4653, plain, (![A_393, B_391, E_390]: (k1_partfun1(A_393, B_391, '#skF_4', '#skF_3', E_390, '#skF_6')=k5_relat_1(E_390, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_390, k1_zfmisc_1(k2_zfmisc_1(A_393, B_391))) | ~v1_funct_1(E_390))), inference(resolution, [status(thm)], [c_76, c_4643])).
% 7.11/2.47  tff(c_6389, plain, (![A_471, B_472, E_473]: (k1_partfun1(A_471, B_472, '#skF_4', '#skF_3', E_473, '#skF_6')=k5_relat_1(E_473, '#skF_6') | ~m1_subset_1(E_473, k1_zfmisc_1(k2_zfmisc_1(A_471, B_472))) | ~v1_funct_1(E_473))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4653])).
% 7.11/2.47  tff(c_6416, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_6389])).
% 7.11/2.47  tff(c_6430, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_6416])).
% 7.11/2.47  tff(c_7001, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6430, c_60])).
% 7.11/2.47  tff(c_7007, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_7001])).
% 7.11/2.47  tff(c_4144, plain, (![D_355, C_356, A_357, B_358]: (D_355=C_356 | ~r2_relset_1(A_357, B_358, C_356, D_355) | ~m1_subset_1(D_355, k1_zfmisc_1(k2_zfmisc_1(A_357, B_358))) | ~m1_subset_1(C_356, k1_zfmisc_1(k2_zfmisc_1(A_357, B_358))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.11/2.47  tff(c_4154, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_74, c_4144])).
% 7.11/2.47  tff(c_4173, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_4154])).
% 7.11/2.47  tff(c_7099, plain, (k5_relat_1('#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7007, c_6430, c_6430, c_4173])).
% 7.11/2.47  tff(c_36, plain, (![A_28, B_30]: (r1_tarski(k2_relat_1(k5_relat_1(A_28, B_30)), k2_relat_1(B_30)) | ~v1_relat_1(B_30) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.11/2.47  tff(c_7118, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_3')), k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7099, c_36])).
% 7.11/2.47  tff(c_7124, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3574, c_3577, c_90, c_7118])).
% 7.11/2.47  tff(c_3696, plain, (![B_318, A_319]: (r1_tarski(k2_relat_1(B_318), A_319) | ~v5_relat_1(B_318, A_319) | ~v1_relat_1(B_318))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.11/2.47  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.11/2.47  tff(c_3718, plain, (![B_318, A_319]: (k2_relat_1(B_318)=A_319 | ~r1_tarski(A_319, k2_relat_1(B_318)) | ~v5_relat_1(B_318, A_319) | ~v1_relat_1(B_318))), inference(resolution, [status(thm)], [c_3696, c_12])).
% 7.11/2.47  tff(c_7128, plain, (k2_relat_1('#skF_6')='#skF_3' | ~v5_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_7124, c_3718])).
% 7.11/2.47  tff(c_7141, plain, (k2_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3577, c_3813, c_7128])).
% 7.11/2.47  tff(c_3875, plain, (![B_333, A_334]: (v5_relat_1(B_333, A_334) | ~r1_tarski(k2_relat_1(B_333), A_334) | ~v1_relat_1(B_333))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.11/2.47  tff(c_3899, plain, (![B_333]: (v5_relat_1(B_333, k2_relat_1(B_333)) | ~v1_relat_1(B_333))), inference(resolution, [status(thm)], [c_16, c_3875])).
% 7.11/2.47  tff(c_3921, plain, (![B_337]: (v2_funct_2(B_337, k2_relat_1(B_337)) | ~v5_relat_1(B_337, k2_relat_1(B_337)) | ~v1_relat_1(B_337))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.11/2.47  tff(c_3935, plain, (![B_333]: (v2_funct_2(B_333, k2_relat_1(B_333)) | ~v1_relat_1(B_333))), inference(resolution, [status(thm)], [c_3899, c_3921])).
% 7.11/2.47  tff(c_7167, plain, (v2_funct_2('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7141, c_3935])).
% 7.11/2.47  tff(c_7191, plain, (v2_funct_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3577, c_7167])).
% 7.11/2.47  tff(c_7193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3455, c_7191])).
% 7.11/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.11/2.47  
% 7.11/2.47  Inference rules
% 7.11/2.47  ----------------------
% 7.11/2.47  #Ref     : 0
% 7.11/2.47  #Sup     : 1646
% 7.11/2.47  #Fact    : 0
% 7.11/2.47  #Define  : 0
% 7.11/2.47  #Split   : 16
% 7.11/2.47  #Chain   : 0
% 7.11/2.47  #Close   : 0
% 7.11/2.47  
% 7.11/2.47  Ordering : KBO
% 7.11/2.47  
% 7.11/2.47  Simplification rules
% 7.11/2.47  ----------------------
% 7.11/2.47  #Subsume      : 180
% 7.11/2.47  #Demod        : 1492
% 7.11/2.47  #Tautology    : 778
% 7.11/2.47  #SimpNegUnit  : 6
% 7.11/2.47  #BackRed      : 86
% 7.11/2.47  
% 7.11/2.47  #Partial instantiations: 0
% 7.11/2.47  #Strategies tried      : 1
% 7.11/2.47  
% 7.11/2.47  Timing (in seconds)
% 7.11/2.47  ----------------------
% 7.11/2.47  Preprocessing        : 0.38
% 7.11/2.47  Parsing              : 0.20
% 7.11/2.47  CNF conversion       : 0.03
% 7.11/2.47  Main loop            : 1.31
% 7.11/2.47  Inferencing          : 0.42
% 7.11/2.47  Reduction            : 0.47
% 7.11/2.47  Demodulation         : 0.34
% 7.11/2.47  BG Simplification    : 0.05
% 7.11/2.47  Subsumption          : 0.27
% 7.11/2.47  Abstraction          : 0.06
% 7.11/2.47  MUC search           : 0.00
% 7.11/2.47  Cooper               : 0.00
% 7.11/2.47  Total                : 1.74
% 7.11/2.47  Index Insertion      : 0.00
% 7.11/2.47  Index Deletion       : 0.00
% 7.11/2.47  Index Matching       : 0.00
% 7.11/2.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
