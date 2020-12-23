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
% DateTime   : Thu Dec  3 10:12:16 EST 2020

% Result     : Theorem 10.21s
% Output     : CNFRefutation 10.57s
% Verified   : 
% Statistics : Number of formulae       :  208 (1196 expanded)
%              Number of leaves         :   53 ( 417 expanded)
%              Depth                    :   15
%              Number of atoms          :  391 (2818 expanded)
%              Number of equality atoms :   92 ( 858 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff(f_156,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_198,negated_conjecture,(
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

tff(f_154,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_124,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_144,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_104,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_178,axiom,(
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

tff(f_77,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

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

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_74,plain,(
    ! [A_55] : k6_relat_1(A_55) = k6_partfun1(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_52,plain,(
    ! [A_32] : v2_funct_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_96,plain,(
    ! [A_32] : v2_funct_1(k6_partfun1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_52])).

tff(c_94,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_90,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_88,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_84,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1520,plain,(
    ! [D_228,B_225,E_224,C_223,F_226,A_227] :
      ( k1_partfun1(A_227,B_225,C_223,D_228,E_224,F_226) = k5_relat_1(E_224,F_226)
      | ~ m1_subset_1(F_226,k1_zfmisc_1(k2_zfmisc_1(C_223,D_228)))
      | ~ v1_funct_1(F_226)
      | ~ m1_subset_1(E_224,k1_zfmisc_1(k2_zfmisc_1(A_227,B_225)))
      | ~ v1_funct_1(E_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1527,plain,(
    ! [A_227,B_225,E_224] :
      ( k1_partfun1(A_227,B_225,'#skF_4','#skF_3',E_224,'#skF_6') = k5_relat_1(E_224,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_224,k1_zfmisc_1(k2_zfmisc_1(A_227,B_225)))
      | ~ v1_funct_1(E_224) ) ),
    inference(resolution,[status(thm)],[c_84,c_1520])).

tff(c_2162,plain,(
    ! [A_284,B_285,E_286] :
      ( k1_partfun1(A_284,B_285,'#skF_4','#skF_3',E_286,'#skF_6') = k5_relat_1(E_286,'#skF_6')
      | ~ m1_subset_1(E_286,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285)))
      | ~ v1_funct_1(E_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1527])).

tff(c_2187,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_2162])).

tff(c_2203,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2187])).

tff(c_62,plain,(
    ! [A_40] : m1_subset_1(k6_relat_1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_95,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_62])).

tff(c_82,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1205,plain,(
    ! [D_190,C_191,A_192,B_193] :
      ( D_190 = C_191
      | ~ r2_relset_1(A_192,B_193,C_191,D_190)
      | ~ m1_subset_1(D_190,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193)))
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1211,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_82,c_1205])).

tff(c_1222,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_1211])).

tff(c_2728,plain,
    ( k5_relat_1('#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2203,c_2203,c_1222])).

tff(c_2729,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2728])).

tff(c_68,plain,(
    ! [E_47,F_48,D_46,C_45,A_43,B_44] :
      ( m1_subset_1(k1_partfun1(A_43,B_44,C_45,D_46,E_47,F_48),k1_zfmisc_1(k2_zfmisc_1(A_43,D_46)))
      | ~ m1_subset_1(F_48,k1_zfmisc_1(k2_zfmisc_1(C_45,D_46)))
      | ~ v1_funct_1(F_48)
      | ~ m1_subset_1(E_47,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_1(E_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2612,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2203,c_68])).

tff(c_2619,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_88,c_84,c_2612])).

tff(c_2831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2729,c_2619])).

tff(c_2832,plain,(
    k5_relat_1('#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2728])).

tff(c_80,plain,
    ( ~ v2_funct_2('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_133,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_46,plain,(
    ! [A_31] : k1_relat_1(k6_relat_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_99,plain,(
    ! [A_31] : k1_relat_1(k6_partfun1(A_31)) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_46])).

tff(c_50,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_97,plain,(
    ! [A_32] : v1_relat_1(k6_partfun1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_50])).

tff(c_146,plain,(
    ! [A_76] :
      ( k1_relat_1(A_76) != k1_xboole_0
      | k1_xboole_0 = A_76
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_152,plain,(
    ! [A_32] :
      ( k1_relat_1(k6_partfun1(A_32)) != k1_xboole_0
      | k6_partfun1(A_32) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_97,c_146])).

tff(c_157,plain,(
    ! [A_77] :
      ( k1_xboole_0 != A_77
      | k6_partfun1(A_77) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_152])).

tff(c_166,plain,
    ( r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_xboole_0)
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_82])).

tff(c_220,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_92,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_86,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_78,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2609,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k5_relat_1('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2203,c_78])).

tff(c_2616,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_90,c_88,c_86,c_84,c_2609])).

tff(c_2617,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_220,c_2616])).

tff(c_2835,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2832,c_2617])).

tff(c_2841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2835])).

tff(c_2843,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_176,plain,(
    ! [A_77] :
      ( v2_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_77 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_96])).

tff(c_211,plain,(
    ! [A_77] : k1_xboole_0 != A_77 ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_218,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_211])).

tff(c_219,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_2844,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_219])).

tff(c_48,plain,(
    ! [A_31] : k2_relat_1(k6_relat_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_98,plain,(
    ! [A_31] : k2_relat_1(k6_partfun1(A_31)) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_48])).

tff(c_169,plain,(
    ! [A_77] :
      ( k2_relat_1(k1_xboole_0) = A_77
      | k1_xboole_0 != A_77 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_98])).

tff(c_2856,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_2843,c_169])).

tff(c_36,plain,(
    ! [A_24,B_25] : v1_relat_1(k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2931,plain,(
    ! [B_332,A_333] :
      ( v1_relat_1(B_332)
      | ~ m1_subset_1(B_332,k1_zfmisc_1(A_333))
      | ~ v1_relat_1(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2943,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_90,c_2931])).

tff(c_2953,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2943])).

tff(c_44,plain,(
    ! [A_30] :
      ( k1_relat_1(A_30) != k1_xboole_0
      | k1_xboole_0 = A_30
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3159,plain,(
    ! [A_349] :
      ( k1_relat_1(A_349) != '#skF_3'
      | A_349 = '#skF_3'
      | ~ v1_relat_1(A_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_2843,c_44])).

tff(c_3175,plain,
    ( k1_relat_1('#skF_5') != '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2953,c_3159])).

tff(c_3184,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3175])).

tff(c_155,plain,(
    ! [A_32] :
      ( k1_xboole_0 != A_32
      | k6_partfun1(A_32) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_152])).

tff(c_2847,plain,(
    ! [A_32] :
      ( A_32 != '#skF_3'
      | k6_partfun1(A_32) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_2843,c_155])).

tff(c_2921,plain,(
    ! [A_327,B_328] :
      ( r2_hidden('#skF_2'(A_327,B_328),A_327)
      | r1_tarski(A_327,B_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2925,plain,(
    ! [A_327,B_328] :
      ( ~ v1_xboole_0(A_327)
      | r1_tarski(A_327,B_328) ) ),
    inference(resolution,[status(thm)],[c_2921,c_2])).

tff(c_3329,plain,(
    ! [B_369,A_370] :
      ( v4_relat_1(B_369,A_370)
      | ~ r1_tarski(k1_relat_1(B_369),A_370)
      | ~ v1_relat_1(B_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3392,plain,(
    ! [B_380,B_381] :
      ( v4_relat_1(B_380,B_381)
      | ~ v1_relat_1(B_380)
      | ~ v1_xboole_0(k1_relat_1(B_380)) ) ),
    inference(resolution,[status(thm)],[c_2925,c_3329])).

tff(c_3394,plain,(
    ! [A_31,B_381] :
      ( v4_relat_1(k6_partfun1(A_31),B_381)
      | ~ v1_relat_1(k6_partfun1(A_31))
      | ~ v1_xboole_0(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_3392])).

tff(c_3397,plain,(
    ! [A_382,B_383] :
      ( v4_relat_1(k6_partfun1(A_382),B_383)
      | ~ v1_xboole_0(A_382) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_3394])).

tff(c_3403,plain,(
    ! [B_383,A_32] :
      ( v4_relat_1('#skF_3',B_383)
      | ~ v1_xboole_0(A_32)
      | A_32 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2847,c_3397])).

tff(c_3405,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3403])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2849,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_12])).

tff(c_3407,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3405,c_2849])).

tff(c_3408,plain,(
    ! [B_383] : v4_relat_1('#skF_3',B_383) ),
    inference(splitRight,[status(thm)],[c_3403])).

tff(c_3409,plain,(
    ! [B_384,A_385] :
      ( r1_tarski(k1_relat_1(B_384),A_385)
      | ~ v4_relat_1(B_384,A_385)
      | ~ v1_relat_1(B_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3430,plain,(
    ! [A_31,A_385] :
      ( r1_tarski(A_31,A_385)
      | ~ v4_relat_1(k6_partfun1(A_31),A_385)
      | ~ v1_relat_1(k6_partfun1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_3409])).

tff(c_3442,plain,(
    ! [A_387,A_388] :
      ( r1_tarski(A_387,A_388)
      | ~ v4_relat_1(k6_partfun1(A_387),A_388) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_3430])).

tff(c_3465,plain,(
    ! [A_32,A_388] :
      ( r1_tarski(A_32,A_388)
      | ~ v4_relat_1('#skF_3',A_388)
      | A_32 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2847,c_3442])).

tff(c_3480,plain,(
    ! [A_389,A_390] :
      ( r1_tarski(A_389,A_390)
      | A_389 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3408,c_3465])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3185,plain,(
    ! [B_350,A_351] :
      ( v1_xboole_0(B_350)
      | ~ m1_subset_1(B_350,k1_zfmisc_1(A_351))
      | ~ v1_xboole_0(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3198,plain,(
    ! [A_15,B_16] :
      ( v1_xboole_0(A_15)
      | ~ v1_xboole_0(B_16)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_24,c_3185])).

tff(c_3510,plain,(
    ! [A_389,A_390] :
      ( v1_xboole_0(A_389)
      | ~ v1_xboole_0(A_390)
      | A_389 != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_3480,c_3198])).

tff(c_3623,plain,(
    ! [A_390] : ~ v1_xboole_0(A_390) ),
    inference(splitLeft,[status(thm)],[c_3510])).

tff(c_3631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3623,c_2849])).

tff(c_3633,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3510])).

tff(c_3257,plain,(
    ! [C_358,A_359,B_360] :
      ( v4_relat_1(C_358,A_359)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_359,B_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3274,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_3257])).

tff(c_10229,plain,(
    ! [B_774,A_775] :
      ( v1_xboole_0(k1_relat_1(B_774))
      | ~ v1_xboole_0(A_775)
      | ~ v4_relat_1(B_774,A_775)
      | ~ v1_relat_1(B_774) ) ),
    inference(resolution,[status(thm)],[c_3409,c_3198])).

tff(c_10261,plain,
    ( v1_xboole_0(k1_relat_1('#skF_5'))
    | ~ v1_xboole_0('#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3274,c_10229])).

tff(c_10301,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2953,c_3633,c_10261])).

tff(c_2991,plain,(
    ! [B_336,A_337] :
      ( B_336 = A_337
      | ~ r1_tarski(B_336,A_337)
      | ~ r1_tarski(A_337,B_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3021,plain,(
    ! [B_339,A_340] :
      ( B_339 = A_340
      | ~ r1_tarski(B_339,A_340)
      | ~ v1_xboole_0(A_340) ) ),
    inference(resolution,[status(thm)],[c_2925,c_2991])).

tff(c_3043,plain,(
    ! [B_341,A_342] :
      ( B_341 = A_342
      | ~ v1_xboole_0(B_341)
      | ~ v1_xboole_0(A_342) ) ),
    inference(resolution,[status(thm)],[c_2925,c_3021])).

tff(c_3048,plain,(
    ! [A_342] :
      ( A_342 = '#skF_3'
      | ~ v1_xboole_0(A_342) ) ),
    inference(resolution,[status(thm)],[c_2849,c_3043])).

tff(c_10332,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10301,c_3048])).

tff(c_10355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3184,c_10332])).

tff(c_10356,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3175])).

tff(c_42,plain,(
    ! [A_30] :
      ( k2_relat_1(A_30) != k1_xboole_0
      | k1_xboole_0 = A_30
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3124,plain,(
    ! [A_346] :
      ( k2_relat_1(A_346) != '#skF_3'
      | A_346 = '#skF_3'
      | ~ v1_relat_1(A_346) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_2843,c_42])).

tff(c_3140,plain,
    ( k2_relat_1('#skF_5') != '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2953,c_3124])).

tff(c_3156,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3140])).

tff(c_10358,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10356,c_3156])).

tff(c_10368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2856,c_10358])).

tff(c_10369,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3140])).

tff(c_10375,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10369,c_133])).

tff(c_10381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2844,c_10375])).

tff(c_10382,plain,(
    ~ v2_funct_2('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_10654,plain,(
    ! [B_810,A_811] :
      ( v1_relat_1(B_810)
      | ~ m1_subset_1(B_810,k1_zfmisc_1(A_811))
      | ~ v1_relat_1(A_811) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10663,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_84,c_10654])).

tff(c_10673,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10663])).

tff(c_10718,plain,(
    ! [C_814,B_815,A_816] :
      ( v5_relat_1(C_814,B_815)
      | ~ m1_subset_1(C_814,k1_zfmisc_1(k2_zfmisc_1(A_816,B_815))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10734,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_10718])).

tff(c_34,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k2_relat_1(B_23),A_22)
      | ~ v5_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10666,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_90,c_10654])).

tff(c_10676,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10666])).

tff(c_11674,plain,(
    ! [C_915,E_916,F_918,D_920,B_917,A_919] :
      ( k1_partfun1(A_919,B_917,C_915,D_920,E_916,F_918) = k5_relat_1(E_916,F_918)
      | ~ m1_subset_1(F_918,k1_zfmisc_1(k2_zfmisc_1(C_915,D_920)))
      | ~ v1_funct_1(F_918)
      | ~ m1_subset_1(E_916,k1_zfmisc_1(k2_zfmisc_1(A_919,B_917)))
      | ~ v1_funct_1(E_916) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_11681,plain,(
    ! [A_919,B_917,E_916] :
      ( k1_partfun1(A_919,B_917,'#skF_4','#skF_3',E_916,'#skF_6') = k5_relat_1(E_916,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_916,k1_zfmisc_1(k2_zfmisc_1(A_919,B_917)))
      | ~ v1_funct_1(E_916) ) ),
    inference(resolution,[status(thm)],[c_84,c_11674])).

tff(c_11995,plain,(
    ! [A_959,B_960,E_961] :
      ( k1_partfun1(A_959,B_960,'#skF_4','#skF_3',E_961,'#skF_6') = k5_relat_1(E_961,'#skF_6')
      | ~ m1_subset_1(E_961,k1_zfmisc_1(k2_zfmisc_1(A_959,B_960)))
      | ~ v1_funct_1(E_961) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_11681])).

tff(c_12011,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_11995])).

tff(c_12020,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_12011])).

tff(c_12147,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12020,c_68])).

tff(c_12154,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_88,c_84,c_12147])).

tff(c_11282,plain,(
    ! [D_875,C_876,A_877,B_878] :
      ( D_875 = C_876
      | ~ r2_relset_1(A_877,B_878,C_876,D_875)
      | ~ m1_subset_1(D_875,k1_zfmisc_1(k2_zfmisc_1(A_877,B_878)))
      | ~ m1_subset_1(C_876,k1_zfmisc_1(k2_zfmisc_1(A_877,B_878))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_11288,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_82,c_11282])).

tff(c_11299,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_11288])).

tff(c_11441,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_11299])).

tff(c_12792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12154,c_12020,c_11441])).

tff(c_12793,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_11299])).

tff(c_12979,plain,(
    ! [D_1029,B_1026,C_1024,F_1027,A_1028,E_1025] :
      ( k1_partfun1(A_1028,B_1026,C_1024,D_1029,E_1025,F_1027) = k5_relat_1(E_1025,F_1027)
      | ~ m1_subset_1(F_1027,k1_zfmisc_1(k2_zfmisc_1(C_1024,D_1029)))
      | ~ v1_funct_1(F_1027)
      | ~ m1_subset_1(E_1025,k1_zfmisc_1(k2_zfmisc_1(A_1028,B_1026)))
      | ~ v1_funct_1(E_1025) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_12986,plain,(
    ! [A_1028,B_1026,E_1025] :
      ( k1_partfun1(A_1028,B_1026,'#skF_4','#skF_3',E_1025,'#skF_6') = k5_relat_1(E_1025,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1025,k1_zfmisc_1(k2_zfmisc_1(A_1028,B_1026)))
      | ~ v1_funct_1(E_1025) ) ),
    inference(resolution,[status(thm)],[c_84,c_12979])).

tff(c_13346,plain,(
    ! [A_1074,B_1075,E_1076] :
      ( k1_partfun1(A_1074,B_1075,'#skF_4','#skF_3',E_1076,'#skF_6') = k5_relat_1(E_1076,'#skF_6')
      | ~ m1_subset_1(E_1076,k1_zfmisc_1(k2_zfmisc_1(A_1074,B_1075)))
      | ~ v1_funct_1(E_1076) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_12986])).

tff(c_13362,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_13346])).

tff(c_13371,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_13362])).

tff(c_13705,plain,(
    k5_relat_1('#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12793,c_13371])).

tff(c_40,plain,(
    ! [A_27,B_29] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_27,B_29)),k2_relat_1(B_29))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_13732,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_3')),k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_13705,c_40])).

tff(c_13736,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10676,c_10673,c_98,c_13732])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13758,plain,
    ( k2_relat_1('#skF_6') = '#skF_3'
    | ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_13736,c_14])).

tff(c_13824,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_13758])).

tff(c_13843,plain,
    ( ~ v5_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_13824])).

tff(c_13852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10673,c_10734,c_13843])).

tff(c_13853,plain,(
    k2_relat_1('#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_13758])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10770,plain,(
    ! [B_824,A_825] :
      ( v5_relat_1(B_824,A_825)
      | ~ r1_tarski(k2_relat_1(B_824),A_825)
      | ~ v1_relat_1(B_824) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10785,plain,(
    ! [B_824] :
      ( v5_relat_1(B_824,k2_relat_1(B_824))
      | ~ v1_relat_1(B_824) ) ),
    inference(resolution,[status(thm)],[c_18,c_10770])).

tff(c_11090,plain,(
    ! [B_854] :
      ( v2_funct_2(B_854,k2_relat_1(B_854))
      | ~ v5_relat_1(B_854,k2_relat_1(B_854))
      | ~ v1_relat_1(B_854) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_11108,plain,(
    ! [B_824] :
      ( v2_funct_2(B_824,k2_relat_1(B_824))
      | ~ v1_relat_1(B_824) ) ),
    inference(resolution,[status(thm)],[c_10785,c_11090])).

tff(c_13866,plain,
    ( v2_funct_2('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_13853,c_11108])).

tff(c_13887,plain,(
    v2_funct_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10673,c_13866])).

tff(c_13889,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10382,c_13887])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:30:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.21/3.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.40/3.76  
% 10.40/3.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.40/3.76  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 10.40/3.76  
% 10.40/3.76  %Foreground sorts:
% 10.40/3.76  
% 10.40/3.76  
% 10.40/3.76  %Background operators:
% 10.40/3.76  
% 10.40/3.76  
% 10.40/3.76  %Foreground operators:
% 10.40/3.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.40/3.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.40/3.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.40/3.76  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.40/3.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.40/3.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.40/3.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.40/3.76  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.40/3.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.40/3.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.40/3.76  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.40/3.76  tff('#skF_5', type, '#skF_5': $i).
% 10.40/3.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.40/3.76  tff('#skF_6', type, '#skF_6': $i).
% 10.40/3.76  tff('#skF_3', type, '#skF_3': $i).
% 10.40/3.76  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 10.40/3.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.40/3.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.40/3.76  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.40/3.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.40/3.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.40/3.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.40/3.76  tff('#skF_4', type, '#skF_4': $i).
% 10.40/3.76  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.40/3.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.40/3.76  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.40/3.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.40/3.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.40/3.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.40/3.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.40/3.76  
% 10.57/3.79  tff(f_156, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.57/3.79  tff(f_108, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 10.57/3.79  tff(f_198, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 10.57/3.79  tff(f_154, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.57/3.79  tff(f_124, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 10.57/3.79  tff(f_122, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.57/3.79  tff(f_144, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.57/3.79  tff(f_104, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 10.57/3.79  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 10.57/3.79  tff(f_178, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 10.57/3.79  tff(f_77, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.57/3.79  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.57/3.79  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.57/3.79  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.57/3.79  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 10.57/3.79  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.57/3.79  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.57/3.79  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 10.57/3.79  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.57/3.79  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.57/3.79  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 10.57/3.79  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 10.57/3.79  tff(f_132, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 10.57/3.79  tff(c_74, plain, (![A_55]: (k6_relat_1(A_55)=k6_partfun1(A_55))), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.57/3.79  tff(c_52, plain, (![A_32]: (v2_funct_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 10.57/3.79  tff(c_96, plain, (![A_32]: (v2_funct_1(k6_partfun1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_52])).
% 10.57/3.79  tff(c_94, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.57/3.79  tff(c_90, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.57/3.79  tff(c_88, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.57/3.79  tff(c_84, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.57/3.79  tff(c_1520, plain, (![D_228, B_225, E_224, C_223, F_226, A_227]: (k1_partfun1(A_227, B_225, C_223, D_228, E_224, F_226)=k5_relat_1(E_224, F_226) | ~m1_subset_1(F_226, k1_zfmisc_1(k2_zfmisc_1(C_223, D_228))) | ~v1_funct_1(F_226) | ~m1_subset_1(E_224, k1_zfmisc_1(k2_zfmisc_1(A_227, B_225))) | ~v1_funct_1(E_224))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.57/3.79  tff(c_1527, plain, (![A_227, B_225, E_224]: (k1_partfun1(A_227, B_225, '#skF_4', '#skF_3', E_224, '#skF_6')=k5_relat_1(E_224, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_224, k1_zfmisc_1(k2_zfmisc_1(A_227, B_225))) | ~v1_funct_1(E_224))), inference(resolution, [status(thm)], [c_84, c_1520])).
% 10.57/3.79  tff(c_2162, plain, (![A_284, B_285, E_286]: (k1_partfun1(A_284, B_285, '#skF_4', '#skF_3', E_286, '#skF_6')=k5_relat_1(E_286, '#skF_6') | ~m1_subset_1(E_286, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))) | ~v1_funct_1(E_286))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1527])).
% 10.57/3.79  tff(c_2187, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_90, c_2162])).
% 10.57/3.79  tff(c_2203, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2187])).
% 10.57/3.79  tff(c_62, plain, (![A_40]: (m1_subset_1(k6_relat_1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.57/3.79  tff(c_95, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_62])).
% 10.57/3.79  tff(c_82, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.57/3.79  tff(c_1205, plain, (![D_190, C_191, A_192, B_193]: (D_190=C_191 | ~r2_relset_1(A_192, B_193, C_191, D_190) | ~m1_subset_1(D_190, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 10.57/3.79  tff(c_1211, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_82, c_1205])).
% 10.57/3.79  tff(c_1222, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_1211])).
% 10.57/3.79  tff(c_2728, plain, (k5_relat_1('#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2203, c_2203, c_1222])).
% 10.57/3.79  tff(c_2729, plain, (~m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_2728])).
% 10.57/3.79  tff(c_68, plain, (![E_47, F_48, D_46, C_45, A_43, B_44]: (m1_subset_1(k1_partfun1(A_43, B_44, C_45, D_46, E_47, F_48), k1_zfmisc_1(k2_zfmisc_1(A_43, D_46))) | ~m1_subset_1(F_48, k1_zfmisc_1(k2_zfmisc_1(C_45, D_46))) | ~v1_funct_1(F_48) | ~m1_subset_1(E_47, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_1(E_47))), inference(cnfTransformation, [status(thm)], [f_144])).
% 10.57/3.79  tff(c_2612, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2203, c_68])).
% 10.57/3.79  tff(c_2619, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_88, c_84, c_2612])).
% 10.57/3.79  tff(c_2831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2729, c_2619])).
% 10.57/3.79  tff(c_2832, plain, (k5_relat_1('#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_2728])).
% 10.57/3.79  tff(c_80, plain, (~v2_funct_2('#skF_6', '#skF_3') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.57/3.79  tff(c_133, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_80])).
% 10.57/3.79  tff(c_46, plain, (![A_31]: (k1_relat_1(k6_relat_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.57/3.79  tff(c_99, plain, (![A_31]: (k1_relat_1(k6_partfun1(A_31))=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_46])).
% 10.57/3.79  tff(c_50, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 10.57/3.79  tff(c_97, plain, (![A_32]: (v1_relat_1(k6_partfun1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_50])).
% 10.57/3.79  tff(c_146, plain, (![A_76]: (k1_relat_1(A_76)!=k1_xboole_0 | k1_xboole_0=A_76 | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.57/3.79  tff(c_152, plain, (![A_32]: (k1_relat_1(k6_partfun1(A_32))!=k1_xboole_0 | k6_partfun1(A_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_97, c_146])).
% 10.57/3.79  tff(c_157, plain, (![A_77]: (k1_xboole_0!=A_77 | k6_partfun1(A_77)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_99, c_152])).
% 10.57/3.79  tff(c_166, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_xboole_0) | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_157, c_82])).
% 10.57/3.79  tff(c_220, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_166])).
% 10.57/3.79  tff(c_92, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.57/3.79  tff(c_86, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.57/3.79  tff(c_78, plain, (![E_61, D_59, A_56, B_57, C_58]: (k1_xboole_0=C_58 | v2_funct_1(D_59) | ~v2_funct_1(k1_partfun1(A_56, B_57, B_57, C_58, D_59, E_61)) | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(B_57, C_58))) | ~v1_funct_2(E_61, B_57, C_58) | ~v1_funct_1(E_61) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_2(D_59, A_56, B_57) | ~v1_funct_1(D_59))), inference(cnfTransformation, [status(thm)], [f_178])).
% 10.57/3.79  tff(c_2609, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k5_relat_1('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2203, c_78])).
% 10.57/3.79  tff(c_2616, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k5_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_90, c_88, c_86, c_84, c_2609])).
% 10.57/3.79  tff(c_2617, plain, (~v2_funct_1(k5_relat_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_133, c_220, c_2616])).
% 10.57/3.79  tff(c_2835, plain, (~v2_funct_1(k6_partfun1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2832, c_2617])).
% 10.57/3.79  tff(c_2841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_2835])).
% 10.57/3.79  tff(c_2843, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_166])).
% 10.57/3.79  tff(c_176, plain, (![A_77]: (v2_funct_1(k1_xboole_0) | k1_xboole_0!=A_77)), inference(superposition, [status(thm), theory('equality')], [c_157, c_96])).
% 10.57/3.79  tff(c_211, plain, (![A_77]: (k1_xboole_0!=A_77)), inference(splitLeft, [status(thm)], [c_176])).
% 10.57/3.79  tff(c_218, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_211])).
% 10.57/3.79  tff(c_219, plain, (v2_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_176])).
% 10.57/3.79  tff(c_2844, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_219])).
% 10.57/3.79  tff(c_48, plain, (![A_31]: (k2_relat_1(k6_relat_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.57/3.79  tff(c_98, plain, (![A_31]: (k2_relat_1(k6_partfun1(A_31))=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_48])).
% 10.57/3.79  tff(c_169, plain, (![A_77]: (k2_relat_1(k1_xboole_0)=A_77 | k1_xboole_0!=A_77)), inference(superposition, [status(thm), theory('equality')], [c_157, c_98])).
% 10.57/3.79  tff(c_2856, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_2843, c_169])).
% 10.57/3.79  tff(c_36, plain, (![A_24, B_25]: (v1_relat_1(k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.57/3.79  tff(c_2931, plain, (![B_332, A_333]: (v1_relat_1(B_332) | ~m1_subset_1(B_332, k1_zfmisc_1(A_333)) | ~v1_relat_1(A_333))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.57/3.79  tff(c_2943, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_2931])).
% 10.57/3.79  tff(c_2953, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2943])).
% 10.57/3.79  tff(c_44, plain, (![A_30]: (k1_relat_1(A_30)!=k1_xboole_0 | k1_xboole_0=A_30 | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.57/3.79  tff(c_3159, plain, (![A_349]: (k1_relat_1(A_349)!='#skF_3' | A_349='#skF_3' | ~v1_relat_1(A_349))), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_2843, c_44])).
% 10.57/3.79  tff(c_3175, plain, (k1_relat_1('#skF_5')!='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_2953, c_3159])).
% 10.57/3.79  tff(c_3184, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_3175])).
% 10.57/3.79  tff(c_155, plain, (![A_32]: (k1_xboole_0!=A_32 | k6_partfun1(A_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_99, c_152])).
% 10.57/3.79  tff(c_2847, plain, (![A_32]: (A_32!='#skF_3' | k6_partfun1(A_32)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_2843, c_155])).
% 10.57/3.79  tff(c_2921, plain, (![A_327, B_328]: (r2_hidden('#skF_2'(A_327, B_328), A_327) | r1_tarski(A_327, B_328))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.57/3.79  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.57/3.79  tff(c_2925, plain, (![A_327, B_328]: (~v1_xboole_0(A_327) | r1_tarski(A_327, B_328))), inference(resolution, [status(thm)], [c_2921, c_2])).
% 10.57/3.79  tff(c_3329, plain, (![B_369, A_370]: (v4_relat_1(B_369, A_370) | ~r1_tarski(k1_relat_1(B_369), A_370) | ~v1_relat_1(B_369))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.57/3.79  tff(c_3392, plain, (![B_380, B_381]: (v4_relat_1(B_380, B_381) | ~v1_relat_1(B_380) | ~v1_xboole_0(k1_relat_1(B_380)))), inference(resolution, [status(thm)], [c_2925, c_3329])).
% 10.57/3.79  tff(c_3394, plain, (![A_31, B_381]: (v4_relat_1(k6_partfun1(A_31), B_381) | ~v1_relat_1(k6_partfun1(A_31)) | ~v1_xboole_0(A_31))), inference(superposition, [status(thm), theory('equality')], [c_99, c_3392])).
% 10.57/3.79  tff(c_3397, plain, (![A_382, B_383]: (v4_relat_1(k6_partfun1(A_382), B_383) | ~v1_xboole_0(A_382))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_3394])).
% 10.57/3.79  tff(c_3403, plain, (![B_383, A_32]: (v4_relat_1('#skF_3', B_383) | ~v1_xboole_0(A_32) | A_32!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2847, c_3397])).
% 10.57/3.79  tff(c_3405, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_3403])).
% 10.57/3.79  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.57/3.79  tff(c_2849, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_12])).
% 10.57/3.79  tff(c_3407, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3405, c_2849])).
% 10.57/3.79  tff(c_3408, plain, (![B_383]: (v4_relat_1('#skF_3', B_383))), inference(splitRight, [status(thm)], [c_3403])).
% 10.57/3.79  tff(c_3409, plain, (![B_384, A_385]: (r1_tarski(k1_relat_1(B_384), A_385) | ~v4_relat_1(B_384, A_385) | ~v1_relat_1(B_384))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.57/3.79  tff(c_3430, plain, (![A_31, A_385]: (r1_tarski(A_31, A_385) | ~v4_relat_1(k6_partfun1(A_31), A_385) | ~v1_relat_1(k6_partfun1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_3409])).
% 10.57/3.79  tff(c_3442, plain, (![A_387, A_388]: (r1_tarski(A_387, A_388) | ~v4_relat_1(k6_partfun1(A_387), A_388))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_3430])).
% 10.57/3.79  tff(c_3465, plain, (![A_32, A_388]: (r1_tarski(A_32, A_388) | ~v4_relat_1('#skF_3', A_388) | A_32!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2847, c_3442])).
% 10.57/3.79  tff(c_3480, plain, (![A_389, A_390]: (r1_tarski(A_389, A_390) | A_389!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3408, c_3465])).
% 10.57/3.79  tff(c_24, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.57/3.79  tff(c_3185, plain, (![B_350, A_351]: (v1_xboole_0(B_350) | ~m1_subset_1(B_350, k1_zfmisc_1(A_351)) | ~v1_xboole_0(A_351))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.57/3.79  tff(c_3198, plain, (![A_15, B_16]: (v1_xboole_0(A_15) | ~v1_xboole_0(B_16) | ~r1_tarski(A_15, B_16))), inference(resolution, [status(thm)], [c_24, c_3185])).
% 10.57/3.79  tff(c_3510, plain, (![A_389, A_390]: (v1_xboole_0(A_389) | ~v1_xboole_0(A_390) | A_389!='#skF_3')), inference(resolution, [status(thm)], [c_3480, c_3198])).
% 10.57/3.79  tff(c_3623, plain, (![A_390]: (~v1_xboole_0(A_390))), inference(splitLeft, [status(thm)], [c_3510])).
% 10.57/3.79  tff(c_3631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3623, c_2849])).
% 10.57/3.79  tff(c_3633, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_3510])).
% 10.57/3.79  tff(c_3257, plain, (![C_358, A_359, B_360]: (v4_relat_1(C_358, A_359) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_359, B_360))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 10.57/3.79  tff(c_3274, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_90, c_3257])).
% 10.57/3.79  tff(c_10229, plain, (![B_774, A_775]: (v1_xboole_0(k1_relat_1(B_774)) | ~v1_xboole_0(A_775) | ~v4_relat_1(B_774, A_775) | ~v1_relat_1(B_774))), inference(resolution, [status(thm)], [c_3409, c_3198])).
% 10.57/3.79  tff(c_10261, plain, (v1_xboole_0(k1_relat_1('#skF_5')) | ~v1_xboole_0('#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3274, c_10229])).
% 10.57/3.79  tff(c_10301, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2953, c_3633, c_10261])).
% 10.57/3.79  tff(c_2991, plain, (![B_336, A_337]: (B_336=A_337 | ~r1_tarski(B_336, A_337) | ~r1_tarski(A_337, B_336))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.57/3.79  tff(c_3021, plain, (![B_339, A_340]: (B_339=A_340 | ~r1_tarski(B_339, A_340) | ~v1_xboole_0(A_340))), inference(resolution, [status(thm)], [c_2925, c_2991])).
% 10.57/3.79  tff(c_3043, plain, (![B_341, A_342]: (B_341=A_342 | ~v1_xboole_0(B_341) | ~v1_xboole_0(A_342))), inference(resolution, [status(thm)], [c_2925, c_3021])).
% 10.57/3.79  tff(c_3048, plain, (![A_342]: (A_342='#skF_3' | ~v1_xboole_0(A_342))), inference(resolution, [status(thm)], [c_2849, c_3043])).
% 10.57/3.79  tff(c_10332, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_10301, c_3048])).
% 10.57/3.79  tff(c_10355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3184, c_10332])).
% 10.57/3.79  tff(c_10356, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_3175])).
% 10.57/3.79  tff(c_42, plain, (![A_30]: (k2_relat_1(A_30)!=k1_xboole_0 | k1_xboole_0=A_30 | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.57/3.79  tff(c_3124, plain, (![A_346]: (k2_relat_1(A_346)!='#skF_3' | A_346='#skF_3' | ~v1_relat_1(A_346))), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_2843, c_42])).
% 10.57/3.79  tff(c_3140, plain, (k2_relat_1('#skF_5')!='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_2953, c_3124])).
% 10.57/3.79  tff(c_3156, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_3140])).
% 10.57/3.79  tff(c_10358, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10356, c_3156])).
% 10.57/3.79  tff(c_10368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2856, c_10358])).
% 10.57/3.79  tff(c_10369, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_3140])).
% 10.57/3.79  tff(c_10375, plain, (~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10369, c_133])).
% 10.57/3.79  tff(c_10381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2844, c_10375])).
% 10.57/3.79  tff(c_10382, plain, (~v2_funct_2('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_80])).
% 10.57/3.79  tff(c_10654, plain, (![B_810, A_811]: (v1_relat_1(B_810) | ~m1_subset_1(B_810, k1_zfmisc_1(A_811)) | ~v1_relat_1(A_811))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.57/3.79  tff(c_10663, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_84, c_10654])).
% 10.57/3.79  tff(c_10673, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_10663])).
% 10.57/3.79  tff(c_10718, plain, (![C_814, B_815, A_816]: (v5_relat_1(C_814, B_815) | ~m1_subset_1(C_814, k1_zfmisc_1(k2_zfmisc_1(A_816, B_815))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 10.57/3.79  tff(c_10734, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_84, c_10718])).
% 10.57/3.79  tff(c_34, plain, (![B_23, A_22]: (r1_tarski(k2_relat_1(B_23), A_22) | ~v5_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.57/3.79  tff(c_10666, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_10654])).
% 10.57/3.79  tff(c_10676, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_10666])).
% 10.57/3.79  tff(c_11674, plain, (![C_915, E_916, F_918, D_920, B_917, A_919]: (k1_partfun1(A_919, B_917, C_915, D_920, E_916, F_918)=k5_relat_1(E_916, F_918) | ~m1_subset_1(F_918, k1_zfmisc_1(k2_zfmisc_1(C_915, D_920))) | ~v1_funct_1(F_918) | ~m1_subset_1(E_916, k1_zfmisc_1(k2_zfmisc_1(A_919, B_917))) | ~v1_funct_1(E_916))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.57/3.79  tff(c_11681, plain, (![A_919, B_917, E_916]: (k1_partfun1(A_919, B_917, '#skF_4', '#skF_3', E_916, '#skF_6')=k5_relat_1(E_916, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_916, k1_zfmisc_1(k2_zfmisc_1(A_919, B_917))) | ~v1_funct_1(E_916))), inference(resolution, [status(thm)], [c_84, c_11674])).
% 10.57/3.79  tff(c_11995, plain, (![A_959, B_960, E_961]: (k1_partfun1(A_959, B_960, '#skF_4', '#skF_3', E_961, '#skF_6')=k5_relat_1(E_961, '#skF_6') | ~m1_subset_1(E_961, k1_zfmisc_1(k2_zfmisc_1(A_959, B_960))) | ~v1_funct_1(E_961))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_11681])).
% 10.57/3.79  tff(c_12011, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_90, c_11995])).
% 10.57/3.79  tff(c_12020, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_12011])).
% 10.57/3.79  tff(c_12147, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12020, c_68])).
% 10.57/3.79  tff(c_12154, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_88, c_84, c_12147])).
% 10.57/3.79  tff(c_11282, plain, (![D_875, C_876, A_877, B_878]: (D_875=C_876 | ~r2_relset_1(A_877, B_878, C_876, D_875) | ~m1_subset_1(D_875, k1_zfmisc_1(k2_zfmisc_1(A_877, B_878))) | ~m1_subset_1(C_876, k1_zfmisc_1(k2_zfmisc_1(A_877, B_878))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 10.57/3.79  tff(c_11288, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_82, c_11282])).
% 10.57/3.79  tff(c_11299, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_11288])).
% 10.57/3.79  tff(c_11441, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_11299])).
% 10.57/3.79  tff(c_12792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12154, c_12020, c_11441])).
% 10.57/3.79  tff(c_12793, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_11299])).
% 10.57/3.79  tff(c_12979, plain, (![D_1029, B_1026, C_1024, F_1027, A_1028, E_1025]: (k1_partfun1(A_1028, B_1026, C_1024, D_1029, E_1025, F_1027)=k5_relat_1(E_1025, F_1027) | ~m1_subset_1(F_1027, k1_zfmisc_1(k2_zfmisc_1(C_1024, D_1029))) | ~v1_funct_1(F_1027) | ~m1_subset_1(E_1025, k1_zfmisc_1(k2_zfmisc_1(A_1028, B_1026))) | ~v1_funct_1(E_1025))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.57/3.79  tff(c_12986, plain, (![A_1028, B_1026, E_1025]: (k1_partfun1(A_1028, B_1026, '#skF_4', '#skF_3', E_1025, '#skF_6')=k5_relat_1(E_1025, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1025, k1_zfmisc_1(k2_zfmisc_1(A_1028, B_1026))) | ~v1_funct_1(E_1025))), inference(resolution, [status(thm)], [c_84, c_12979])).
% 10.57/3.79  tff(c_13346, plain, (![A_1074, B_1075, E_1076]: (k1_partfun1(A_1074, B_1075, '#skF_4', '#skF_3', E_1076, '#skF_6')=k5_relat_1(E_1076, '#skF_6') | ~m1_subset_1(E_1076, k1_zfmisc_1(k2_zfmisc_1(A_1074, B_1075))) | ~v1_funct_1(E_1076))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_12986])).
% 10.57/3.79  tff(c_13362, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_90, c_13346])).
% 10.57/3.79  tff(c_13371, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_13362])).
% 10.57/3.79  tff(c_13705, plain, (k5_relat_1('#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12793, c_13371])).
% 10.57/3.79  tff(c_40, plain, (![A_27, B_29]: (r1_tarski(k2_relat_1(k5_relat_1(A_27, B_29)), k2_relat_1(B_29)) | ~v1_relat_1(B_29) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.57/3.79  tff(c_13732, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_3')), k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_13705, c_40])).
% 10.57/3.79  tff(c_13736, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_10676, c_10673, c_98, c_13732])).
% 10.57/3.79  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.57/3.79  tff(c_13758, plain, (k2_relat_1('#skF_6')='#skF_3' | ~r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_13736, c_14])).
% 10.57/3.79  tff(c_13824, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_13758])).
% 10.57/3.79  tff(c_13843, plain, (~v5_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_13824])).
% 10.57/3.79  tff(c_13852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10673, c_10734, c_13843])).
% 10.57/3.79  tff(c_13853, plain, (k2_relat_1('#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_13758])).
% 10.57/3.79  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.57/3.79  tff(c_10770, plain, (![B_824, A_825]: (v5_relat_1(B_824, A_825) | ~r1_tarski(k2_relat_1(B_824), A_825) | ~v1_relat_1(B_824))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.57/3.79  tff(c_10785, plain, (![B_824]: (v5_relat_1(B_824, k2_relat_1(B_824)) | ~v1_relat_1(B_824))), inference(resolution, [status(thm)], [c_18, c_10770])).
% 10.57/3.79  tff(c_11090, plain, (![B_854]: (v2_funct_2(B_854, k2_relat_1(B_854)) | ~v5_relat_1(B_854, k2_relat_1(B_854)) | ~v1_relat_1(B_854))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.57/3.79  tff(c_11108, plain, (![B_824]: (v2_funct_2(B_824, k2_relat_1(B_824)) | ~v1_relat_1(B_824))), inference(resolution, [status(thm)], [c_10785, c_11090])).
% 10.57/3.79  tff(c_13866, plain, (v2_funct_2('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_13853, c_11108])).
% 10.57/3.79  tff(c_13887, plain, (v2_funct_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10673, c_13866])).
% 10.57/3.79  tff(c_13889, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10382, c_13887])).
% 10.57/3.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.57/3.79  
% 10.57/3.79  Inference rules
% 10.57/3.79  ----------------------
% 10.57/3.79  #Ref     : 29
% 10.57/3.79  #Sup     : 3208
% 10.57/3.79  #Fact    : 0
% 10.57/3.79  #Define  : 0
% 10.57/3.79  #Split   : 75
% 10.57/3.79  #Chain   : 0
% 10.57/3.79  #Close   : 0
% 10.57/3.79  
% 10.57/3.79  Ordering : KBO
% 10.57/3.79  
% 10.57/3.79  Simplification rules
% 10.57/3.79  ----------------------
% 10.57/3.79  #Subsume      : 1439
% 10.57/3.79  #Demod        : 1399
% 10.57/3.79  #Tautology    : 608
% 10.57/3.79  #SimpNegUnit  : 179
% 10.57/3.79  #BackRed      : 129
% 10.57/3.79  
% 10.57/3.79  #Partial instantiations: 0
% 10.57/3.79  #Strategies tried      : 1
% 10.57/3.79  
% 10.57/3.79  Timing (in seconds)
% 10.57/3.79  ----------------------
% 10.57/3.79  Preprocessing        : 0.38
% 10.57/3.80  Parsing              : 0.21
% 10.57/3.80  CNF conversion       : 0.03
% 10.57/3.80  Main loop            : 2.57
% 10.57/3.80  Inferencing          : 0.71
% 10.57/3.80  Reduction            : 0.95
% 10.57/3.80  Demodulation         : 0.68
% 10.57/3.80  BG Simplification    : 0.07
% 10.57/3.80  Subsumption          : 0.64
% 10.57/3.80  Abstraction          : 0.08
% 10.57/3.80  MUC search           : 0.00
% 10.57/3.80  Cooper               : 0.00
% 10.57/3.80  Total                : 3.01
% 10.57/3.80  Index Insertion      : 0.00
% 10.57/3.80  Index Deletion       : 0.00
% 10.57/3.80  Index Matching       : 0.00
% 10.57/3.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
