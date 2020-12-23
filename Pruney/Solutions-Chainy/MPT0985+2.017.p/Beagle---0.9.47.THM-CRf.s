%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:27 EST 2020

% Result     : Theorem 5.41s
% Output     : CNFRefutation 5.67s
% Verified   : 
% Statistics : Number of formulae       :  253 (2307 expanded)
%              Number of leaves         :   43 ( 769 expanded)
%              Depth                    :   16
%              Number of atoms          :  458 (6476 expanded)
%              Number of equality atoms :  119 (1436 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_227,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_xboole_0(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_236,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_227])).

tff(c_238,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_176,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_185,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_176])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2969,plain,(
    ! [A_232,B_233,C_234] :
      ( k2_relset_1(A_232,B_233,C_234) = k2_relat_1(C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2985,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2969])).

tff(c_2992,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2985])).

tff(c_32,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    ! [A_9] :
      ( v1_funct_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_118,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_121,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_118])).

tff(c_124,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_121])).

tff(c_143,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_150,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_143])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_150])).

tff(c_156,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_239,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_243,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_239])).

tff(c_390,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_403,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_390])).

tff(c_409,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_403])).

tff(c_26,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_285,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_294,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_285])).

tff(c_799,plain,(
    ! [B_106,A_107,C_108] :
      ( k1_xboole_0 = B_106
      | k1_relset_1(A_107,B_106,C_108) = A_107
      | ~ v1_funct_2(C_108,A_107,B_106)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_818,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_799])).

tff(c_830,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_294,c_818])).

tff(c_831,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_830])).

tff(c_255,plain,(
    ! [A_61] :
      ( k2_relat_1(k2_funct_1(A_61)) = k1_relat_1(A_61)
      | ~ v2_funct_1(A_61)
      | ~ v1_funct_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    ! [A_7] :
      ( k10_relat_1(A_7,k2_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1168,plain,(
    ! [A_131] :
      ( k10_relat_1(k2_funct_1(A_131),k1_relat_1(A_131)) = k1_relat_1(k2_funct_1(A_131))
      | ~ v1_relat_1(k2_funct_1(A_131))
      | ~ v2_funct_1(A_131)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_16])).

tff(c_1177,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_831,c_1168])).

tff(c_1187,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_76,c_70,c_1177])).

tff(c_1196,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1187])).

tff(c_1199,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1196])).

tff(c_1203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_76,c_1199])).

tff(c_1205,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1187])).

tff(c_157,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_419,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_16])).

tff(c_427,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_419])).

tff(c_837,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_427])).

tff(c_270,plain,(
    ! [A_62] :
      ( k1_relat_1(k2_funct_1(A_62)) = k2_relat_1(A_62)
      | ~ v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    ! [A_6] :
      ( k9_relat_1(A_6,k1_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1223,plain,(
    ! [A_135] :
      ( k9_relat_1(k2_funct_1(A_135),k2_relat_1(A_135)) = k2_relat_1(k2_funct_1(A_135))
      | ~ v1_relat_1(k2_funct_1(A_135))
      | ~ v2_funct_1(A_135)
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_14])).

tff(c_1239,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_1223])).

tff(c_1249,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_76,c_70,c_1205,c_1239])).

tff(c_28,plain,(
    ! [B_11,A_10] :
      ( k9_relat_1(k2_funct_1(B_11),A_10) = k10_relat_1(B_11,A_10)
      | ~ v2_funct_1(B_11)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1255,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1249,c_28])).

tff(c_1262,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_76,c_70,c_837,c_1255])).

tff(c_326,plain,(
    ! [A_73] :
      ( m1_subset_1(A_73,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_73),k2_relat_1(A_73))))
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_354,plain,(
    ! [A_73] :
      ( r1_tarski(A_73,k2_zfmisc_1(k1_relat_1(A_73),k2_relat_1(A_73)))
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_326,c_8])).

tff(c_1283,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1262,c_354])).

tff(c_1312,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_157,c_1283])).

tff(c_1364,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1312])).

tff(c_1377,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_76,c_70,c_409,c_1364])).

tff(c_1379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_1377])).

tff(c_1380,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_830])).

tff(c_44,plain,(
    ! [C_28,A_26] :
      ( k1_xboole_0 = C_28
      | ~ v1_funct_2(C_28,A_26,k1_xboole_0)
      | k1_xboole_0 = A_26
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1676,plain,(
    ! [C_150,A_151] :
      ( C_150 = '#skF_2'
      | ~ v1_funct_2(C_150,A_151,'#skF_2')
      | A_151 = '#skF_2'
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_151,'#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_1380,c_1380,c_1380,c_44])).

tff(c_1694,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_72,c_1676])).

tff(c_1706,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1694])).

tff(c_1707,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1706])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1402,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_2])).

tff(c_1720,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1707,c_1402])).

tff(c_1740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_1720])).

tff(c_1741,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1706])).

tff(c_1755,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_1402])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1400,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_1380,c_20])).

tff(c_1754,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_1741,c_1400])).

tff(c_54,plain,(
    ! [A_29] :
      ( m1_subset_1(A_29,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_29),k2_relat_1(A_29))))
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_413,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_54])).

tff(c_423,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_76,c_413])).

tff(c_36,plain,(
    ! [C_19,A_16,B_17] :
      ( v1_xboole_0(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_455,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_423,c_36])).

tff(c_459,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_1837,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1754,c_459])).

tff(c_1840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1755,c_1837])).

tff(c_1841,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1865,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1841,c_4])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1882,plain,(
    ! [A_2] : r1_tarski('#skF_3',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1865,c_6])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1880,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1865,c_1865,c_18])).

tff(c_1881,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1865,c_1865,c_20])).

tff(c_2127,plain,(
    ! [B_164,A_165] :
      ( m1_subset_1(B_164,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_164),A_165)))
      | ~ r1_tarski(k2_relat_1(B_164),A_165)
      | ~ v1_funct_1(B_164)
      | ~ v1_relat_1(B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2149,plain,(
    ! [A_165] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_165)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_165)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1881,c_2127])).

tff(c_2160,plain,(
    ! [A_165] : m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_165))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_76,c_1882,c_1880,c_2149])).

tff(c_2505,plain,(
    ! [A_200] :
      ( k10_relat_1(k2_funct_1(A_200),k1_relat_1(A_200)) = k1_relat_1(k2_funct_1(A_200))
      | ~ v1_relat_1(k2_funct_1(A_200))
      | ~ v2_funct_1(A_200)
      | ~ v1_funct_1(A_200)
      | ~ v1_relat_1(A_200) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_16])).

tff(c_2514,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1881,c_2505])).

tff(c_2521,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_76,c_70,c_2514])).

tff(c_2522,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2521])).

tff(c_2525,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_2522])).

tff(c_2529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_76,c_2525])).

tff(c_2531,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2521])).

tff(c_381,plain,(
    ! [A_74] :
      ( v1_xboole_0(A_74)
      | ~ v1_xboole_0(k1_relat_1(A_74))
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(resolution,[status(thm)],[c_326,c_36])).

tff(c_2710,plain,(
    ! [A_213] :
      ( v1_xboole_0(k2_funct_1(A_213))
      | ~ v1_xboole_0(k2_relat_1(A_213))
      | ~ v1_funct_1(k2_funct_1(A_213))
      | ~ v1_relat_1(k2_funct_1(A_213))
      | ~ v2_funct_1(A_213)
      | ~ v1_funct_1(A_213)
      | ~ v1_relat_1(A_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_381])).

tff(c_2716,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1880,c_2710])).

tff(c_2723,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_76,c_70,c_2531,c_157,c_1841,c_2716])).

tff(c_1877,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1865,c_4])).

tff(c_2733,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2723,c_1877])).

tff(c_1905,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1880,c_409])).

tff(c_1931,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1905,c_239])).

tff(c_2742,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2733,c_1931])).

tff(c_2751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2160,c_2742])).

tff(c_2752,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_2753,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_2870,plain,(
    ! [A_222,B_223,C_224] :
      ( k1_relset_1(A_222,B_223,C_224) = k1_relat_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2890,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2753,c_2870])).

tff(c_3537,plain,(
    ! [B_269,C_270,A_271] :
      ( k1_xboole_0 = B_269
      | v1_funct_2(C_270,A_271,B_269)
      | k1_relset_1(A_271,B_269,C_270) != A_271
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_271,B_269))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3549,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_2753,c_3537])).

tff(c_3563,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2890,c_3549])).

tff(c_3564,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2752,c_3563])).

tff(c_3569,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3564])).

tff(c_3572,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3569])).

tff(c_3575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_76,c_70,c_2992,c_3572])).

tff(c_3576,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3564])).

tff(c_3599,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3576,c_2])).

tff(c_3601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_3599])).

tff(c_3603,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_4627,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3603,c_4])).

tff(c_3602,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_4613,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3602,c_4])).

tff(c_4647,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4627,c_4613])).

tff(c_86,plain,(
    ! [A_33] :
      ( v1_relat_1(A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_90,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_86])).

tff(c_91,plain,(
    ! [A_34] :
      ( v1_funct_1(A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_95,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_91])).

tff(c_216,plain,(
    ! [A_54] :
      ( v1_funct_2(A_54,k1_relat_1(A_54),k2_relat_1(A_54))
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_219,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_216])).

tff(c_224,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_95,c_20,c_219])).

tff(c_4630,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4613,c_4613,c_4613,c_224])).

tff(c_4748,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4647,c_4647,c_4647,c_4630])).

tff(c_4671,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4647,c_68])).

tff(c_4636,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4613,c_4613,c_18])).

tff(c_4683,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4647,c_4647,c_4636])).

tff(c_4670,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4647,c_72])).

tff(c_4912,plain,(
    ! [A_366,B_367,C_368] :
      ( k2_relset_1(A_366,B_367,C_368) = k2_relat_1(C_368)
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(A_366,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4921,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4670,c_4912])).

tff(c_4929,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4671,c_4683,c_4921])).

tff(c_12,plain,(
    ! [A_5] :
      ( v1_relat_1(A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3630,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3603,c_12])).

tff(c_22,plain,(
    ! [A_8] :
      ( v1_funct_1(A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3629,plain,(
    v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3603,c_22])).

tff(c_3628,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3603,c_4])).

tff(c_3614,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3602,c_4])).

tff(c_3648,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3628,c_3614])).

tff(c_3639,plain,(
    ! [A_2] : r1_tarski('#skF_3',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3614,c_6])).

tff(c_3704,plain,(
    ! [A_2] : r1_tarski('#skF_1',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3648,c_3639])).

tff(c_3637,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3614,c_3614,c_18])).

tff(c_3674,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3648,c_3648,c_3637])).

tff(c_3638,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3614,c_3614,c_20])).

tff(c_3689,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3648,c_3648,c_3638])).

tff(c_4125,plain,(
    ! [B_313,A_314] :
      ( m1_subset_1(B_313,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_313),A_314)))
      | ~ r1_tarski(k2_relat_1(B_313),A_314)
      | ~ v1_funct_1(B_313)
      | ~ v1_relat_1(B_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4150,plain,(
    ! [A_314] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_314)))
      | ~ r1_tarski(k2_relat_1('#skF_1'),A_314)
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3689,c_4125])).

tff(c_4158,plain,(
    ! [A_314] : m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_314))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3630,c_3629,c_3704,c_3674,c_4150])).

tff(c_3665,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3648,c_70])).

tff(c_3754,plain,(
    ! [A_275] :
      ( k2_relat_1(k2_funct_1(A_275)) = k1_relat_1(A_275)
      | ~ v2_funct_1(A_275)
      | ~ v1_funct_1(A_275)
      | ~ v1_relat_1(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4405,plain,(
    ! [A_345] :
      ( k10_relat_1(k2_funct_1(A_345),k1_relat_1(A_345)) = k1_relat_1(k2_funct_1(A_345))
      | ~ v1_relat_1(k2_funct_1(A_345))
      | ~ v2_funct_1(A_345)
      | ~ v1_funct_1(A_345)
      | ~ v1_relat_1(A_345) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3754,c_16])).

tff(c_4417,plain,
    ( k10_relat_1(k2_funct_1('#skF_1'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3689,c_4405])).

tff(c_4421,plain,
    ( k10_relat_1(k2_funct_1('#skF_1'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3630,c_3629,c_3665,c_4417])).

tff(c_4422,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4421])).

tff(c_4425,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_4422])).

tff(c_4429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3630,c_3629,c_4425])).

tff(c_4431,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4421])).

tff(c_3660,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3648,c_157])).

tff(c_3790,plain,(
    ! [A_276] :
      ( m1_subset_1(A_276,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_276),k2_relat_1(A_276))))
      | ~ v1_funct_1(A_276)
      | ~ v1_relat_1(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3843,plain,(
    ! [A_280] :
      ( v1_xboole_0(A_280)
      | ~ v1_xboole_0(k1_relat_1(A_280))
      | ~ v1_funct_1(A_280)
      | ~ v1_relat_1(A_280) ) ),
    inference(resolution,[status(thm)],[c_3790,c_36])).

tff(c_4554,plain,(
    ! [A_347] :
      ( v1_xboole_0(k2_funct_1(A_347))
      | ~ v1_xboole_0(k2_relat_1(A_347))
      | ~ v1_funct_1(k2_funct_1(A_347))
      | ~ v1_relat_1(k2_funct_1(A_347))
      | ~ v2_funct_1(A_347)
      | ~ v1_funct_1(A_347)
      | ~ v1_relat_1(A_347) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3843])).

tff(c_4563,plain,
    ( v1_xboole_0(k2_funct_1('#skF_1'))
    | ~ v1_xboole_0('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3674,c_4554])).

tff(c_4567,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3630,c_3629,c_3665,c_4431,c_3660,c_3603,c_4563])).

tff(c_3634,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3614,c_4])).

tff(c_3712,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3648,c_3634])).

tff(c_4577,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4567,c_3712])).

tff(c_3663,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3648,c_68])).

tff(c_3662,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3648,c_72])).

tff(c_3892,plain,(
    ! [A_284,B_285,C_286] :
      ( k2_relset_1(A_284,B_285,C_286) = k2_relat_1(C_286)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3901,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3662,c_3892])).

tff(c_3910,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3663,c_3674,c_3901])).

tff(c_3604,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_3657,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3648,c_3604])).

tff(c_3912,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3910,c_3657])).

tff(c_4589,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4577,c_3912])).

tff(c_4601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4158,c_4589])).

tff(c_4603,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_4661,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4603,c_36])).

tff(c_4771,plain,
    ( v1_xboole_0(k2_funct_1('#skF_1'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4647,c_4661])).

tff(c_4772,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4771])).

tff(c_4937,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4929,c_4772])).

tff(c_4941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3603,c_4937])).

tff(c_4942,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4771])).

tff(c_4633,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4613,c_4])).

tff(c_4741,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4647,c_4633])).

tff(c_4980,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4942,c_4741])).

tff(c_4943,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4771])).

tff(c_4953,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4943,c_4741])).

tff(c_4602,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_4665,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4647,c_4602])).

tff(c_5016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4748,c_4980,c_4953,c_4665])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:47:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.41/2.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.67/2.11  
% 5.67/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.67/2.12  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.67/2.12  
% 5.67/2.12  %Foreground sorts:
% 5.67/2.12  
% 5.67/2.12  
% 5.67/2.12  %Background operators:
% 5.67/2.12  
% 5.67/2.12  
% 5.67/2.12  %Foreground operators:
% 5.67/2.12  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.67/2.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.67/2.12  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.67/2.12  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.67/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.67/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.67/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.67/2.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.67/2.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.67/2.12  tff('#skF_2', type, '#skF_2': $i).
% 5.67/2.12  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.67/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.67/2.12  tff('#skF_1', type, '#skF_1': $i).
% 5.67/2.12  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.67/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.67/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.67/2.12  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.67/2.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.67/2.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.67/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.67/2.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.67/2.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.67/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.67/2.12  
% 5.67/2.14  tff(f_157, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.67/2.14  tff(f_92, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 5.67/2.14  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.67/2.14  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.67/2.14  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.67/2.14  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.67/2.14  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.67/2.14  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.67/2.14  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.67/2.14  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 5.67/2.14  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 5.67/2.14  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 5.67/2.14  tff(f_128, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.67/2.14  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.67/2.14  tff(f_51, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.67/2.14  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.67/2.14  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.67/2.14  tff(f_140, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 5.67/2.14  tff(f_40, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 5.67/2.14  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 5.67/2.14  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.67/2.14  tff(c_227, plain, (![C_55, A_56, B_57]: (v1_xboole_0(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.67/2.14  tff(c_236, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_227])).
% 5.67/2.14  tff(c_238, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_236])).
% 5.67/2.14  tff(c_176, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.67/2.14  tff(c_185, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_176])).
% 5.67/2.14  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.67/2.14  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.67/2.14  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.67/2.14  tff(c_2969, plain, (![A_232, B_233, C_234]: (k2_relset_1(A_232, B_233, C_234)=k2_relat_1(C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.67/2.14  tff(c_2985, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_2969])).
% 5.67/2.14  tff(c_2992, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2985])).
% 5.67/2.14  tff(c_32, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.67/2.14  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.67/2.14  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.67/2.14  tff(c_24, plain, (![A_9]: (v1_funct_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.67/2.14  tff(c_66, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.67/2.14  tff(c_118, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_66])).
% 5.67/2.14  tff(c_121, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_118])).
% 5.67/2.14  tff(c_124, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_121])).
% 5.67/2.14  tff(c_143, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.67/2.14  tff(c_150, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_143])).
% 5.67/2.14  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_150])).
% 5.67/2.14  tff(c_156, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_66])).
% 5.67/2.14  tff(c_239, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_156])).
% 5.67/2.14  tff(c_243, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_10, c_239])).
% 5.67/2.14  tff(c_390, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.67/2.14  tff(c_403, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_390])).
% 5.67/2.14  tff(c_409, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_403])).
% 5.67/2.14  tff(c_26, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.67/2.14  tff(c_285, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.67/2.14  tff(c_294, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_285])).
% 5.67/2.14  tff(c_799, plain, (![B_106, A_107, C_108]: (k1_xboole_0=B_106 | k1_relset_1(A_107, B_106, C_108)=A_107 | ~v1_funct_2(C_108, A_107, B_106) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.67/2.14  tff(c_818, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_799])).
% 5.67/2.14  tff(c_830, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_294, c_818])).
% 5.67/2.14  tff(c_831, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_830])).
% 5.67/2.14  tff(c_255, plain, (![A_61]: (k2_relat_1(k2_funct_1(A_61))=k1_relat_1(A_61) | ~v2_funct_1(A_61) | ~v1_funct_1(A_61) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.67/2.14  tff(c_16, plain, (![A_7]: (k10_relat_1(A_7, k2_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.67/2.14  tff(c_1168, plain, (![A_131]: (k10_relat_1(k2_funct_1(A_131), k1_relat_1(A_131))=k1_relat_1(k2_funct_1(A_131)) | ~v1_relat_1(k2_funct_1(A_131)) | ~v2_funct_1(A_131) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(superposition, [status(thm), theory('equality')], [c_255, c_16])).
% 5.67/2.14  tff(c_1177, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_831, c_1168])).
% 5.67/2.14  tff(c_1187, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_76, c_70, c_1177])).
% 5.67/2.14  tff(c_1196, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1187])).
% 5.67/2.14  tff(c_1199, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1196])).
% 5.67/2.14  tff(c_1203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_76, c_1199])).
% 5.67/2.14  tff(c_1205, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1187])).
% 5.67/2.14  tff(c_157, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_66])).
% 5.67/2.14  tff(c_419, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_409, c_16])).
% 5.67/2.14  tff(c_427, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_419])).
% 5.67/2.14  tff(c_837, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_831, c_427])).
% 5.67/2.14  tff(c_270, plain, (![A_62]: (k1_relat_1(k2_funct_1(A_62))=k2_relat_1(A_62) | ~v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.67/2.14  tff(c_14, plain, (![A_6]: (k9_relat_1(A_6, k1_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.67/2.14  tff(c_1223, plain, (![A_135]: (k9_relat_1(k2_funct_1(A_135), k2_relat_1(A_135))=k2_relat_1(k2_funct_1(A_135)) | ~v1_relat_1(k2_funct_1(A_135)) | ~v2_funct_1(A_135) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(superposition, [status(thm), theory('equality')], [c_270, c_14])).
% 5.67/2.14  tff(c_1239, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_409, c_1223])).
% 5.67/2.14  tff(c_1249, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_76, c_70, c_1205, c_1239])).
% 5.67/2.14  tff(c_28, plain, (![B_11, A_10]: (k9_relat_1(k2_funct_1(B_11), A_10)=k10_relat_1(B_11, A_10) | ~v2_funct_1(B_11) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.67/2.14  tff(c_1255, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1249, c_28])).
% 5.67/2.14  tff(c_1262, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_76, c_70, c_837, c_1255])).
% 5.67/2.14  tff(c_326, plain, (![A_73]: (m1_subset_1(A_73, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_73), k2_relat_1(A_73)))) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.67/2.14  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.67/2.14  tff(c_354, plain, (![A_73]: (r1_tarski(A_73, k2_zfmisc_1(k1_relat_1(A_73), k2_relat_1(A_73))) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_326, c_8])).
% 5.67/2.14  tff(c_1283, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1262, c_354])).
% 5.67/2.14  tff(c_1312, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_157, c_1283])).
% 5.67/2.14  tff(c_1364, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1312])).
% 5.67/2.14  tff(c_1377, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_76, c_70, c_409, c_1364])).
% 5.67/2.14  tff(c_1379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_243, c_1377])).
% 5.67/2.14  tff(c_1380, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_830])).
% 5.67/2.14  tff(c_44, plain, (![C_28, A_26]: (k1_xboole_0=C_28 | ~v1_funct_2(C_28, A_26, k1_xboole_0) | k1_xboole_0=A_26 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.67/2.14  tff(c_1676, plain, (![C_150, A_151]: (C_150='#skF_2' | ~v1_funct_2(C_150, A_151, '#skF_2') | A_151='#skF_2' | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_151, '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_1380, c_1380, c_1380, c_44])).
% 5.67/2.14  tff(c_1694, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_72, c_1676])).
% 5.67/2.14  tff(c_1706, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1694])).
% 5.67/2.14  tff(c_1707, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_1706])).
% 5.67/2.14  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.67/2.14  tff(c_1402, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_2])).
% 5.67/2.14  tff(c_1720, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1707, c_1402])).
% 5.67/2.14  tff(c_1740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_1720])).
% 5.67/2.14  tff(c_1741, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1706])).
% 5.67/2.14  tff(c_1755, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_1402])).
% 5.67/2.14  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.67/2.14  tff(c_1400, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_1380, c_20])).
% 5.67/2.14  tff(c_1754, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_1741, c_1400])).
% 5.67/2.14  tff(c_54, plain, (![A_29]: (m1_subset_1(A_29, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_29), k2_relat_1(A_29)))) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.67/2.14  tff(c_413, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_409, c_54])).
% 5.67/2.14  tff(c_423, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_76, c_413])).
% 5.67/2.14  tff(c_36, plain, (![C_19, A_16, B_17]: (v1_xboole_0(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.67/2.14  tff(c_455, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_423, c_36])).
% 5.67/2.14  tff(c_459, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_455])).
% 5.67/2.14  tff(c_1837, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1754, c_459])).
% 5.67/2.14  tff(c_1840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1755, c_1837])).
% 5.67/2.14  tff(c_1841, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_455])).
% 5.67/2.14  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.67/2.14  tff(c_1865, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1841, c_4])).
% 5.67/2.14  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.67/2.14  tff(c_1882, plain, (![A_2]: (r1_tarski('#skF_3', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_1865, c_6])).
% 5.67/2.14  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.67/2.14  tff(c_1880, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1865, c_1865, c_18])).
% 5.67/2.14  tff(c_1881, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1865, c_1865, c_20])).
% 5.67/2.14  tff(c_2127, plain, (![B_164, A_165]: (m1_subset_1(B_164, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_164), A_165))) | ~r1_tarski(k2_relat_1(B_164), A_165) | ~v1_funct_1(B_164) | ~v1_relat_1(B_164))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.67/2.14  tff(c_2149, plain, (![A_165]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_165))) | ~r1_tarski(k2_relat_1('#skF_3'), A_165) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1881, c_2127])).
% 5.67/2.14  tff(c_2160, plain, (![A_165]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_165))))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_76, c_1882, c_1880, c_2149])).
% 5.67/2.14  tff(c_2505, plain, (![A_200]: (k10_relat_1(k2_funct_1(A_200), k1_relat_1(A_200))=k1_relat_1(k2_funct_1(A_200)) | ~v1_relat_1(k2_funct_1(A_200)) | ~v2_funct_1(A_200) | ~v1_funct_1(A_200) | ~v1_relat_1(A_200))), inference(superposition, [status(thm), theory('equality')], [c_255, c_16])).
% 5.67/2.14  tff(c_2514, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1881, c_2505])).
% 5.67/2.14  tff(c_2521, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_76, c_70, c_2514])).
% 5.67/2.14  tff(c_2522, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2521])).
% 5.67/2.14  tff(c_2525, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_2522])).
% 5.67/2.14  tff(c_2529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_76, c_2525])).
% 5.67/2.14  tff(c_2531, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2521])).
% 5.67/2.14  tff(c_381, plain, (![A_74]: (v1_xboole_0(A_74) | ~v1_xboole_0(k1_relat_1(A_74)) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(resolution, [status(thm)], [c_326, c_36])).
% 5.67/2.14  tff(c_2710, plain, (![A_213]: (v1_xboole_0(k2_funct_1(A_213)) | ~v1_xboole_0(k2_relat_1(A_213)) | ~v1_funct_1(k2_funct_1(A_213)) | ~v1_relat_1(k2_funct_1(A_213)) | ~v2_funct_1(A_213) | ~v1_funct_1(A_213) | ~v1_relat_1(A_213))), inference(superposition, [status(thm), theory('equality')], [c_32, c_381])).
% 5.67/2.14  tff(c_2716, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1880, c_2710])).
% 5.67/2.14  tff(c_2723, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_76, c_70, c_2531, c_157, c_1841, c_2716])).
% 5.67/2.14  tff(c_1877, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1865, c_4])).
% 5.67/2.14  tff(c_2733, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_2723, c_1877])).
% 5.67/2.14  tff(c_1905, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1880, c_409])).
% 5.67/2.14  tff(c_1931, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1905, c_239])).
% 5.67/2.14  tff(c_2742, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2733, c_1931])).
% 5.67/2.14  tff(c_2751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2160, c_2742])).
% 5.67/2.14  tff(c_2752, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_156])).
% 5.67/2.14  tff(c_2753, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_156])).
% 5.67/2.14  tff(c_2870, plain, (![A_222, B_223, C_224]: (k1_relset_1(A_222, B_223, C_224)=k1_relat_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.67/2.14  tff(c_2890, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2753, c_2870])).
% 5.67/2.14  tff(c_3537, plain, (![B_269, C_270, A_271]: (k1_xboole_0=B_269 | v1_funct_2(C_270, A_271, B_269) | k1_relset_1(A_271, B_269, C_270)!=A_271 | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_271, B_269))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.67/2.14  tff(c_3549, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_2753, c_3537])).
% 5.67/2.14  tff(c_3563, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2890, c_3549])).
% 5.67/2.14  tff(c_3564, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2752, c_3563])).
% 5.67/2.14  tff(c_3569, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_3564])).
% 5.67/2.14  tff(c_3572, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_3569])).
% 5.67/2.14  tff(c_3575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_76, c_70, c_2992, c_3572])).
% 5.67/2.14  tff(c_3576, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_3564])).
% 5.67/2.14  tff(c_3599, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3576, c_2])).
% 5.67/2.14  tff(c_3601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_3599])).
% 5.67/2.14  tff(c_3603, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_236])).
% 5.67/2.14  tff(c_4627, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_3603, c_4])).
% 5.67/2.14  tff(c_3602, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_236])).
% 5.67/2.14  tff(c_4613, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3602, c_4])).
% 5.67/2.14  tff(c_4647, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4627, c_4613])).
% 5.67/2.14  tff(c_86, plain, (![A_33]: (v1_relat_1(A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.67/2.14  tff(c_90, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_86])).
% 5.67/2.14  tff(c_91, plain, (![A_34]: (v1_funct_1(A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.67/2.14  tff(c_95, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_91])).
% 5.67/2.14  tff(c_216, plain, (![A_54]: (v1_funct_2(A_54, k1_relat_1(A_54), k2_relat_1(A_54)) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.67/2.14  tff(c_219, plain, (v1_funct_2(k1_xboole_0, k1_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_216])).
% 5.67/2.14  tff(c_224, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_95, c_20, c_219])).
% 5.67/2.14  tff(c_4630, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4613, c_4613, c_4613, c_224])).
% 5.67/2.14  tff(c_4748, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4647, c_4647, c_4647, c_4630])).
% 5.67/2.14  tff(c_4671, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4647, c_68])).
% 5.67/2.14  tff(c_4636, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4613, c_4613, c_18])).
% 5.67/2.14  tff(c_4683, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4647, c_4647, c_4636])).
% 5.67/2.14  tff(c_4670, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4647, c_72])).
% 5.67/2.14  tff(c_4912, plain, (![A_366, B_367, C_368]: (k2_relset_1(A_366, B_367, C_368)=k2_relat_1(C_368) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(A_366, B_367))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.67/2.14  tff(c_4921, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')=k2_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4670, c_4912])).
% 5.67/2.14  tff(c_4929, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4671, c_4683, c_4921])).
% 5.67/2.14  tff(c_12, plain, (![A_5]: (v1_relat_1(A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.67/2.14  tff(c_3630, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3603, c_12])).
% 5.67/2.14  tff(c_22, plain, (![A_8]: (v1_funct_1(A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.67/2.14  tff(c_3629, plain, (v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_3603, c_22])).
% 5.67/2.14  tff(c_3628, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_3603, c_4])).
% 5.67/2.14  tff(c_3614, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3602, c_4])).
% 5.67/2.14  tff(c_3648, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3628, c_3614])).
% 5.67/2.14  tff(c_3639, plain, (![A_2]: (r1_tarski('#skF_3', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_3614, c_6])).
% 5.67/2.14  tff(c_3704, plain, (![A_2]: (r1_tarski('#skF_1', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_3648, c_3639])).
% 5.67/2.14  tff(c_3637, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3614, c_3614, c_18])).
% 5.67/2.14  tff(c_3674, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3648, c_3648, c_3637])).
% 5.67/2.14  tff(c_3638, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3614, c_3614, c_20])).
% 5.67/2.14  tff(c_3689, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3648, c_3648, c_3638])).
% 5.67/2.14  tff(c_4125, plain, (![B_313, A_314]: (m1_subset_1(B_313, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_313), A_314))) | ~r1_tarski(k2_relat_1(B_313), A_314) | ~v1_funct_1(B_313) | ~v1_relat_1(B_313))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.67/2.14  tff(c_4150, plain, (![A_314]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_314))) | ~r1_tarski(k2_relat_1('#skF_1'), A_314) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3689, c_4125])).
% 5.67/2.14  tff(c_4158, plain, (![A_314]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_314))))), inference(demodulation, [status(thm), theory('equality')], [c_3630, c_3629, c_3704, c_3674, c_4150])).
% 5.67/2.14  tff(c_3665, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3648, c_70])).
% 5.67/2.14  tff(c_3754, plain, (![A_275]: (k2_relat_1(k2_funct_1(A_275))=k1_relat_1(A_275) | ~v2_funct_1(A_275) | ~v1_funct_1(A_275) | ~v1_relat_1(A_275))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.67/2.14  tff(c_4405, plain, (![A_345]: (k10_relat_1(k2_funct_1(A_345), k1_relat_1(A_345))=k1_relat_1(k2_funct_1(A_345)) | ~v1_relat_1(k2_funct_1(A_345)) | ~v2_funct_1(A_345) | ~v1_funct_1(A_345) | ~v1_relat_1(A_345))), inference(superposition, [status(thm), theory('equality')], [c_3754, c_16])).
% 5.67/2.14  tff(c_4417, plain, (k10_relat_1(k2_funct_1('#skF_1'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3689, c_4405])).
% 5.67/2.14  tff(c_4421, plain, (k10_relat_1(k2_funct_1('#skF_1'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3630, c_3629, c_3665, c_4417])).
% 5.67/2.14  tff(c_4422, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_4421])).
% 5.67/2.14  tff(c_4425, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_4422])).
% 5.67/2.14  tff(c_4429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3630, c_3629, c_4425])).
% 5.67/2.14  tff(c_4431, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4421])).
% 5.67/2.14  tff(c_3660, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3648, c_157])).
% 5.67/2.14  tff(c_3790, plain, (![A_276]: (m1_subset_1(A_276, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_276), k2_relat_1(A_276)))) | ~v1_funct_1(A_276) | ~v1_relat_1(A_276))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.67/2.14  tff(c_3843, plain, (![A_280]: (v1_xboole_0(A_280) | ~v1_xboole_0(k1_relat_1(A_280)) | ~v1_funct_1(A_280) | ~v1_relat_1(A_280))), inference(resolution, [status(thm)], [c_3790, c_36])).
% 5.67/2.14  tff(c_4554, plain, (![A_347]: (v1_xboole_0(k2_funct_1(A_347)) | ~v1_xboole_0(k2_relat_1(A_347)) | ~v1_funct_1(k2_funct_1(A_347)) | ~v1_relat_1(k2_funct_1(A_347)) | ~v2_funct_1(A_347) | ~v1_funct_1(A_347) | ~v1_relat_1(A_347))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3843])).
% 5.67/2.14  tff(c_4563, plain, (v1_xboole_0(k2_funct_1('#skF_1')) | ~v1_xboole_0('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3674, c_4554])).
% 5.67/2.14  tff(c_4567, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3630, c_3629, c_3665, c_4431, c_3660, c_3603, c_4563])).
% 5.67/2.14  tff(c_3634, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3614, c_4])).
% 5.67/2.14  tff(c_3712, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3648, c_3634])).
% 5.67/2.14  tff(c_4577, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_4567, c_3712])).
% 5.67/2.14  tff(c_3663, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3648, c_68])).
% 5.67/2.14  tff(c_3662, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3648, c_72])).
% 5.67/2.14  tff(c_3892, plain, (![A_284, B_285, C_286]: (k2_relset_1(A_284, B_285, C_286)=k2_relat_1(C_286) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.67/2.14  tff(c_3901, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')=k2_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3662, c_3892])).
% 5.67/2.14  tff(c_3910, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3663, c_3674, c_3901])).
% 5.67/2.14  tff(c_3604, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_156])).
% 5.67/2.14  tff(c_3657, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3648, c_3604])).
% 5.67/2.14  tff(c_3912, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3910, c_3657])).
% 5.67/2.14  tff(c_4589, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4577, c_3912])).
% 5.67/2.14  tff(c_4601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4158, c_4589])).
% 5.67/2.14  tff(c_4603, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_156])).
% 5.67/2.14  tff(c_4661, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_4603, c_36])).
% 5.67/2.14  tff(c_4771, plain, (v1_xboole_0(k2_funct_1('#skF_1')) | ~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4647, c_4661])).
% 5.67/2.14  tff(c_4772, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_4771])).
% 5.67/2.14  tff(c_4937, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4929, c_4772])).
% 5.67/2.14  tff(c_4941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3603, c_4937])).
% 5.67/2.14  tff(c_4942, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4771])).
% 5.67/2.14  tff(c_4633, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4613, c_4])).
% 5.67/2.14  tff(c_4741, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4647, c_4633])).
% 5.67/2.14  tff(c_4980, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_4942, c_4741])).
% 5.67/2.14  tff(c_4943, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_4771])).
% 5.67/2.14  tff(c_4953, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_4943, c_4741])).
% 5.67/2.14  tff(c_4602, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_156])).
% 5.67/2.14  tff(c_4665, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4647, c_4602])).
% 5.67/2.14  tff(c_5016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4748, c_4980, c_4953, c_4665])).
% 5.67/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.67/2.14  
% 5.67/2.14  Inference rules
% 5.67/2.14  ----------------------
% 5.67/2.14  #Ref     : 0
% 5.67/2.14  #Sup     : 1023
% 5.67/2.14  #Fact    : 0
% 5.67/2.14  #Define  : 0
% 5.67/2.14  #Split   : 18
% 5.67/2.14  #Chain   : 0
% 5.67/2.14  #Close   : 0
% 5.67/2.14  
% 5.67/2.14  Ordering : KBO
% 5.67/2.15  
% 5.67/2.15  Simplification rules
% 5.67/2.15  ----------------------
% 5.67/2.15  #Subsume      : 95
% 5.67/2.15  #Demod        : 1612
% 5.67/2.15  #Tautology    : 652
% 5.67/2.15  #SimpNegUnit  : 5
% 5.67/2.15  #BackRed      : 231
% 5.67/2.15  
% 5.67/2.15  #Partial instantiations: 0
% 5.67/2.15  #Strategies tried      : 1
% 5.67/2.15  
% 5.67/2.15  Timing (in seconds)
% 5.67/2.15  ----------------------
% 5.67/2.15  Preprocessing        : 0.37
% 5.67/2.15  Parsing              : 0.21
% 5.67/2.15  CNF conversion       : 0.02
% 5.67/2.15  Main loop            : 0.89
% 5.67/2.15  Inferencing          : 0.32
% 5.67/2.15  Reduction            : 0.31
% 5.67/2.15  Demodulation         : 0.22
% 5.67/2.15  BG Simplification    : 0.04
% 5.67/2.15  Subsumption          : 0.14
% 5.67/2.15  Abstraction          : 0.04
% 5.67/2.15  MUC search           : 0.00
% 5.67/2.15  Cooper               : 0.00
% 5.67/2.15  Total                : 1.34
% 5.67/2.15  Index Insertion      : 0.00
% 5.67/2.15  Index Deletion       : 0.00
% 5.67/2.15  Index Matching       : 0.00
% 5.67/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
