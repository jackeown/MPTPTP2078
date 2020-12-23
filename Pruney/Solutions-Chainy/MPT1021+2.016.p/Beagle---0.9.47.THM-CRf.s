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
% DateTime   : Thu Dec  3 10:16:01 EST 2020

% Result     : Theorem 10.77s
% Output     : CNFRefutation 11.22s
% Verified   : 
% Statistics : Number of formulae       :  279 (8237 expanded)
%              Number of leaves         :   49 (2489 expanded)
%              Depth                    :   23
%              Number of atoms          :  590 (19787 expanded)
%              Number of equality atoms :  150 (8178 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_173,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_138,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_160,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_158,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_148,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_110,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(c_84,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_13669,plain,(
    ! [C_1071,A_1072,B_1073] :
      ( v1_relat_1(C_1071)
      | ~ m1_subset_1(C_1071,k1_zfmisc_1(k2_zfmisc_1(A_1072,B_1073))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_13686,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_13669])).

tff(c_90,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_86,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_14389,plain,(
    ! [C_1179,A_1180,B_1181] :
      ( v2_funct_1(C_1179)
      | ~ v3_funct_2(C_1179,A_1180,B_1181)
      | ~ v1_funct_1(C_1179)
      | ~ m1_subset_1(C_1179,k1_zfmisc_1(k2_zfmisc_1(A_1180,B_1181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14399,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_14389])).

tff(c_14410,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_14399])).

tff(c_74,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_13900,plain,(
    ! [A_1107,B_1108,D_1109] :
      ( r2_relset_1(A_1107,B_1108,D_1109,D_1109)
      | ~ m1_subset_1(D_1109,k1_zfmisc_1(k2_zfmisc_1(A_1107,B_1108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_13912,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_74,c_13900])).

tff(c_13769,plain,(
    ! [C_1083,B_1084,A_1085] :
      ( v5_relat_1(C_1083,B_1084)
      | ~ m1_subset_1(C_1083,k1_zfmisc_1(k2_zfmisc_1(A_1085,B_1084))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_13788,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_13769])).

tff(c_13927,plain,(
    ! [B_1114,A_1115] :
      ( k2_relat_1(B_1114) = A_1115
      | ~ v2_funct_2(B_1114,A_1115)
      | ~ v5_relat_1(B_1114,A_1115)
      | ~ v1_relat_1(B_1114) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_13939,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_13788,c_13927])).

tff(c_13949,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13686,c_13939])).

tff(c_13957,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_13949])).

tff(c_14268,plain,(
    ! [C_1167,B_1168,A_1169] :
      ( v2_funct_2(C_1167,B_1168)
      | ~ v3_funct_2(C_1167,A_1169,B_1168)
      | ~ v1_funct_1(C_1167)
      | ~ m1_subset_1(C_1167,k1_zfmisc_1(k2_zfmisc_1(A_1169,B_1168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14278,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_14268])).

tff(c_14290,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_14278])).

tff(c_14292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13957,c_14290])).

tff(c_14293,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13949])).

tff(c_80,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_26,plain,(
    ! [A_9] :
      ( k5_relat_1(k2_funct_1(A_9),A_9) = k6_relat_1(k2_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_92,plain,(
    ! [A_9] :
      ( k5_relat_1(k2_funct_1(A_9),A_9) = k6_partfun1(k2_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_26])).

tff(c_88,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_14994,plain,(
    ! [A_1275,B_1276] :
      ( k2_funct_2(A_1275,B_1276) = k2_funct_1(B_1276)
      | ~ m1_subset_1(B_1276,k1_zfmisc_1(k2_zfmisc_1(A_1275,A_1275)))
      | ~ v3_funct_2(B_1276,A_1275,A_1275)
      | ~ v1_funct_2(B_1276,A_1275,A_1275)
      | ~ v1_funct_1(B_1276) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_15004,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_14994])).

tff(c_15017,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_15004])).

tff(c_14909,plain,(
    ! [A_1257,B_1258] :
      ( v1_funct_1(k2_funct_2(A_1257,B_1258))
      | ~ m1_subset_1(B_1258,k1_zfmisc_1(k2_zfmisc_1(A_1257,A_1257)))
      | ~ v3_funct_2(B_1258,A_1257,A_1257)
      | ~ v1_funct_2(B_1258,A_1257,A_1257)
      | ~ v1_funct_1(B_1258) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_14919,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_14909])).

tff(c_14932,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_14919])).

tff(c_15018,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15017,c_14932])).

tff(c_64,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k2_funct_2(A_31,B_32),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ v3_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_15427,plain,(
    ! [B_1309,E_1308,F_1307,C_1310,A_1305,D_1306] :
      ( k1_partfun1(A_1305,B_1309,C_1310,D_1306,E_1308,F_1307) = k5_relat_1(E_1308,F_1307)
      | ~ m1_subset_1(F_1307,k1_zfmisc_1(k2_zfmisc_1(C_1310,D_1306)))
      | ~ v1_funct_1(F_1307)
      | ~ m1_subset_1(E_1308,k1_zfmisc_1(k2_zfmisc_1(A_1305,B_1309)))
      | ~ v1_funct_1(E_1308) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_15438,plain,(
    ! [A_1305,B_1309,E_1308] :
      ( k1_partfun1(A_1305,B_1309,'#skF_1','#skF_1',E_1308,'#skF_2') = k5_relat_1(E_1308,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_1308,k1_zfmisc_1(k2_zfmisc_1(A_1305,B_1309)))
      | ~ v1_funct_1(E_1308) ) ),
    inference(resolution,[status(thm)],[c_84,c_15427])).

tff(c_15466,plain,(
    ! [A_1311,B_1312,E_1313] :
      ( k1_partfun1(A_1311,B_1312,'#skF_1','#skF_1',E_1313,'#skF_2') = k5_relat_1(E_1313,'#skF_2')
      | ~ m1_subset_1(E_1313,k1_zfmisc_1(k2_zfmisc_1(A_1311,B_1312)))
      | ~ v1_funct_1(E_1313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_15438])).

tff(c_16053,plain,(
    ! [A_1327,B_1328] :
      ( k1_partfun1(A_1327,A_1327,'#skF_1','#skF_1',k2_funct_2(A_1327,B_1328),'#skF_2') = k5_relat_1(k2_funct_2(A_1327,B_1328),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_1327,B_1328))
      | ~ m1_subset_1(B_1328,k1_zfmisc_1(k2_zfmisc_1(A_1327,A_1327)))
      | ~ v3_funct_2(B_1328,A_1327,A_1327)
      | ~ v1_funct_2(B_1328,A_1327,A_1327)
      | ~ v1_funct_1(B_1328) ) ),
    inference(resolution,[status(thm)],[c_64,c_15466])).

tff(c_16068,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_16053])).

tff(c_16089,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_15018,c_15017,c_15017,c_15017,c_16068])).

tff(c_265,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_282,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_265])).

tff(c_987,plain,(
    ! [C_173,A_174,B_175] :
      ( v2_funct_1(C_173)
      | ~ v3_funct_2(C_173,A_174,B_175)
      | ~ v1_funct_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_997,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_987])).

tff(c_1008,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_997])).

tff(c_452,plain,(
    ! [A_89,B_90,D_91] :
      ( r2_relset_1(A_89,B_90,D_91,D_91)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_464,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_74,c_452])).

tff(c_839,plain,(
    ! [A_150,B_151,C_152] :
      ( k1_relset_1(A_150,B_151,C_152) = k1_relat_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_859,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_839])).

tff(c_1346,plain,(
    ! [B_222,A_223,C_224] :
      ( k1_xboole_0 = B_222
      | k1_relset_1(A_223,B_222,C_224) = A_223
      | ~ v1_funct_2(C_224,A_223,B_222)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_223,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1356,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_1346])).

tff(c_1368,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_859,c_1356])).

tff(c_1370,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1368])).

tff(c_28,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k2_funct_1(A_9)) = k6_relat_1(k1_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_91,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k2_funct_1(A_9)) = k6_partfun1(k1_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_28])).

tff(c_1535,plain,(
    ! [A_259,B_260] :
      ( k2_funct_2(A_259,B_260) = k2_funct_1(B_260)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(k2_zfmisc_1(A_259,A_259)))
      | ~ v3_funct_2(B_260,A_259,A_259)
      | ~ v1_funct_2(B_260,A_259,A_259)
      | ~ v1_funct_1(B_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1545,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_1535])).

tff(c_1558,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_1545])).

tff(c_1501,plain,(
    ! [A_253,B_254] :
      ( v1_funct_1(k2_funct_2(A_253,B_254))
      | ~ m1_subset_1(B_254,k1_zfmisc_1(k2_zfmisc_1(A_253,A_253)))
      | ~ v3_funct_2(B_254,A_253,A_253)
      | ~ v1_funct_2(B_254,A_253,A_253)
      | ~ v1_funct_1(B_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1511,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_1501])).

tff(c_1524,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_1511])).

tff(c_1559,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_1524])).

tff(c_1757,plain,(
    ! [A_281,B_282] :
      ( m1_subset_1(k2_funct_2(A_281,B_282),k1_zfmisc_1(k2_zfmisc_1(A_281,A_281)))
      | ~ m1_subset_1(B_282,k1_zfmisc_1(k2_zfmisc_1(A_281,A_281)))
      | ~ v3_funct_2(B_282,A_281,A_281)
      | ~ v1_funct_2(B_282,A_281,A_281)
      | ~ v1_funct_1(B_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1799,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1558,c_1757])).

tff(c_1823,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_1799])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1893,plain,(
    r1_tarski(k2_funct_1('#skF_2'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1823,c_16])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1954,plain,(
    ! [C_288,D_284,E_286,A_283,F_285,B_287] :
      ( k1_partfun1(A_283,B_287,C_288,D_284,E_286,F_285) = k5_relat_1(E_286,F_285)
      | ~ m1_subset_1(F_285,k1_zfmisc_1(k2_zfmisc_1(C_288,D_284)))
      | ~ v1_funct_1(F_285)
      | ~ m1_subset_1(E_286,k1_zfmisc_1(k2_zfmisc_1(A_283,B_287)))
      | ~ v1_funct_1(E_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_4885,plain,(
    ! [C_379,A_380,A_381,B_378,E_377,D_382] :
      ( k1_partfun1(A_381,B_378,C_379,D_382,E_377,A_380) = k5_relat_1(E_377,A_380)
      | ~ v1_funct_1(A_380)
      | ~ m1_subset_1(E_377,k1_zfmisc_1(k2_zfmisc_1(A_381,B_378)))
      | ~ v1_funct_1(E_377)
      | ~ r1_tarski(A_380,k2_zfmisc_1(C_379,D_382)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1954])).

tff(c_4910,plain,(
    ! [C_379,D_382,A_380] :
      ( k1_partfun1('#skF_1','#skF_1',C_379,D_382,'#skF_2',A_380) = k5_relat_1('#skF_2',A_380)
      | ~ v1_funct_1(A_380)
      | ~ v1_funct_1('#skF_2')
      | ~ r1_tarski(A_380,k2_zfmisc_1(C_379,D_382)) ) ),
    inference(resolution,[status(thm)],[c_84,c_4885])).

tff(c_4945,plain,(
    ! [C_383,D_384,A_385] :
      ( k1_partfun1('#skF_1','#skF_1',C_383,D_384,'#skF_2',A_385) = k5_relat_1('#skF_2',A_385)
      | ~ v1_funct_1(A_385)
      | ~ r1_tarski(A_385,k2_zfmisc_1(C_383,D_384)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_4910])).

tff(c_4972,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1893,c_4945])).

tff(c_5017,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1559,c_4972])).

tff(c_82,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_185,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_1560,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_185])).

tff(c_5024,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5017,c_1560])).

tff(c_5031,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_5024])).

tff(c_5034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_90,c_1008,c_464,c_1370,c_5031])).

tff(c_5035,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1368])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5077,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5035,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5072,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5035,c_5035,c_14])).

tff(c_186,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_194,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_84,c_186])).

tff(c_220,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_227,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_194,c_220])).

tff(c_347,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_5255,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5072,c_347])).

tff(c_5260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5077,c_5255])).

tff(c_5261,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_5271,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5261,c_84])).

tff(c_6597,plain,(
    ! [C_591,A_592,B_593] :
      ( v2_funct_1(C_591)
      | ~ v3_funct_2(C_591,A_592,B_593)
      | ~ v1_funct_1(C_591)
      | ~ m1_subset_1(C_591,k1_zfmisc_1(k2_zfmisc_1(A_592,B_593))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6704,plain,(
    ! [C_606] :
      ( v2_funct_1(C_606)
      | ~ v3_funct_2(C_606,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_606)
      | ~ m1_subset_1(C_606,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5261,c_6597])).

tff(c_6710,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5271,c_6704])).

tff(c_6718,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_6710])).

tff(c_6181,plain,(
    ! [A_532,B_533,D_534] :
      ( r2_relset_1(A_532,B_533,D_534,D_534)
      | ~ m1_subset_1(D_534,k1_zfmisc_1(k2_zfmisc_1(A_532,B_533))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6193,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_74,c_6181])).

tff(c_6227,plain,(
    ! [A_537,B_538,C_539] :
      ( k1_relset_1(A_537,B_538,C_539) = k1_relat_1(C_539)
      | ~ m1_subset_1(C_539,k1_zfmisc_1(k2_zfmisc_1(A_537,B_538))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6289,plain,(
    ! [C_544] :
      ( k1_relset_1('#skF_1','#skF_1',C_544) = k1_relat_1(C_544)
      | ~ m1_subset_1(C_544,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5261,c_6227])).

tff(c_6302,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5271,c_6289])).

tff(c_6843,plain,(
    ! [B_634,C_635,A_636] :
      ( k1_xboole_0 = B_634
      | v1_funct_2(C_635,A_636,B_634)
      | k1_relset_1(A_636,B_634,C_635) != A_636
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1(A_636,B_634))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6846,plain,(
    ! [C_635] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(C_635,'#skF_1','#skF_1')
      | k1_relset_1('#skF_1','#skF_1',C_635) != '#skF_1'
      | ~ m1_subset_1(C_635,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5261,c_6843])).

tff(c_6913,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6846])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5280,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_5261,c_10])).

tff(c_5364,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5280])).

tff(c_6951,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6913,c_5364])).

tff(c_6959,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6913,c_6913,c_14])).

tff(c_7189,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6959,c_5261])).

tff(c_7191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6951,c_7189])).

tff(c_7193,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6846])).

tff(c_7257,plain,(
    ! [B_662,A_663,C_664] :
      ( k1_xboole_0 = B_662
      | k1_relset_1(A_663,B_662,C_664) = A_663
      | ~ v1_funct_2(C_664,A_663,B_662)
      | ~ m1_subset_1(C_664,k1_zfmisc_1(k2_zfmisc_1(A_663,B_662))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_7260,plain,(
    ! [C_664] :
      ( k1_xboole_0 = '#skF_1'
      | k1_relset_1('#skF_1','#skF_1',C_664) = '#skF_1'
      | ~ v1_funct_2(C_664,'#skF_1','#skF_1')
      | ~ m1_subset_1(C_664,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5261,c_7257])).

tff(c_7307,plain,(
    ! [C_667] :
      ( k1_relset_1('#skF_1','#skF_1',C_667) = '#skF_1'
      | ~ v1_funct_2(C_667,'#skF_1','#skF_1')
      | ~ m1_subset_1(C_667,k1_zfmisc_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7193,c_7260])).

tff(c_7313,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_5271,c_7307])).

tff(c_7323,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_6302,c_7313])).

tff(c_7606,plain,(
    ! [A_689,B_690] :
      ( k2_funct_2(A_689,B_690) = k2_funct_1(B_690)
      | ~ m1_subset_1(B_690,k1_zfmisc_1(k2_zfmisc_1(A_689,A_689)))
      | ~ v3_funct_2(B_690,A_689,A_689)
      | ~ v1_funct_2(B_690,A_689,A_689)
      | ~ v1_funct_1(B_690) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_7640,plain,(
    ! [B_693] :
      ( k2_funct_2('#skF_1',B_693) = k2_funct_1(B_693)
      | ~ m1_subset_1(B_693,k1_zfmisc_1('#skF_2'))
      | ~ v3_funct_2(B_693,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_693,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_693) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5261,c_7606])).

tff(c_7646,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5271,c_7640])).

tff(c_7656,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_7646])).

tff(c_7547,plain,(
    ! [A_682,B_683] :
      ( v1_funct_1(k2_funct_2(A_682,B_683))
      | ~ m1_subset_1(B_683,k1_zfmisc_1(k2_zfmisc_1(A_682,A_682)))
      | ~ v3_funct_2(B_683,A_682,A_682)
      | ~ v1_funct_2(B_683,A_682,A_682)
      | ~ v1_funct_1(B_683) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_7585,plain,(
    ! [B_686] :
      ( v1_funct_1(k2_funct_2('#skF_1',B_686))
      | ~ m1_subset_1(B_686,k1_zfmisc_1('#skF_2'))
      | ~ v3_funct_2(B_686,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_686,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_686) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5261,c_7547])).

tff(c_7591,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5271,c_7585])).

tff(c_7601,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_7591])).

tff(c_7658,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7656,c_7601])).

tff(c_7677,plain,(
    ! [A_695,B_696] :
      ( v3_funct_2(k2_funct_2(A_695,B_696),A_695,A_695)
      | ~ m1_subset_1(B_696,k1_zfmisc_1(k2_zfmisc_1(A_695,A_695)))
      | ~ v3_funct_2(B_696,A_695,A_695)
      | ~ v1_funct_2(B_696,A_695,A_695)
      | ~ v1_funct_1(B_696) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_7745,plain,(
    ! [B_701] :
      ( v3_funct_2(k2_funct_2('#skF_1',B_701),'#skF_1','#skF_1')
      | ~ m1_subset_1(B_701,k1_zfmisc_1('#skF_2'))
      | ~ v3_funct_2(B_701,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_701,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_701) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5261,c_7677])).

tff(c_7757,plain,
    ( v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7656,c_7745])).

tff(c_7762,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_5271,c_7757])).

tff(c_6719,plain,(
    ! [A_6] :
      ( v2_funct_1(A_6)
      | ~ v3_funct_2(A_6,'#skF_1','#skF_1')
      | ~ v1_funct_1(A_6)
      | ~ r1_tarski(A_6,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_6704])).

tff(c_7771,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ r1_tarski(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_7762,c_6719])).

tff(c_7780,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ r1_tarski(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7658,c_7771])).

tff(c_7781,plain,(
    ~ r1_tarski(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_7780])).

tff(c_7982,plain,(
    ! [A_710,B_711] :
      ( m1_subset_1(k2_funct_2(A_710,B_711),k1_zfmisc_1(k2_zfmisc_1(A_710,A_710)))
      | ~ m1_subset_1(B_711,k1_zfmisc_1(k2_zfmisc_1(A_710,A_710)))
      | ~ v3_funct_2(B_711,A_710,A_710)
      | ~ v1_funct_2(B_711,A_710,A_710)
      | ~ v1_funct_1(B_711) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_8024,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7656,c_7982])).

tff(c_8051,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_5271,c_5261,c_5261,c_8024])).

tff(c_8089,plain,(
    r1_tarski(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_8051,c_16])).

tff(c_8115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7781,c_8089])).

tff(c_8117,plain,(
    r1_tarski(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_7780])).

tff(c_8462,plain,(
    ! [D_719,C_723,A_718,B_722,F_720,E_721] :
      ( k1_partfun1(A_718,B_722,C_723,D_719,E_721,F_720) = k5_relat_1(E_721,F_720)
      | ~ m1_subset_1(F_720,k1_zfmisc_1(k2_zfmisc_1(C_723,D_719)))
      | ~ v1_funct_1(F_720)
      | ~ m1_subset_1(E_721,k1_zfmisc_1(k2_zfmisc_1(A_718,B_722)))
      | ~ v1_funct_1(E_721) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_11032,plain,(
    ! [A_812,E_811,A_808,B_809,C_813,D_810] :
      ( k1_partfun1(A_808,B_809,C_813,D_810,E_811,A_812) = k5_relat_1(E_811,A_812)
      | ~ v1_funct_1(A_812)
      | ~ m1_subset_1(E_811,k1_zfmisc_1(k2_zfmisc_1(A_808,B_809)))
      | ~ v1_funct_1(E_811)
      | ~ r1_tarski(A_812,k2_zfmisc_1(C_813,D_810)) ) ),
    inference(resolution,[status(thm)],[c_18,c_8462])).

tff(c_11049,plain,(
    ! [C_814,D_815,E_816,A_817] :
      ( k1_partfun1('#skF_1','#skF_1',C_814,D_815,E_816,A_817) = k5_relat_1(E_816,A_817)
      | ~ v1_funct_1(A_817)
      | ~ m1_subset_1(E_816,k1_zfmisc_1('#skF_2'))
      | ~ v1_funct_1(E_816)
      | ~ r1_tarski(A_817,k2_zfmisc_1(C_814,D_815)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5261,c_11032])).

tff(c_11069,plain,(
    ! [C_814,D_815,A_817] :
      ( k1_partfun1('#skF_1','#skF_1',C_814,D_815,'#skF_2',A_817) = k5_relat_1('#skF_2',A_817)
      | ~ v1_funct_1(A_817)
      | ~ v1_funct_1('#skF_2')
      | ~ r1_tarski(A_817,k2_zfmisc_1(C_814,D_815)) ) ),
    inference(resolution,[status(thm)],[c_5271,c_11049])).

tff(c_11100,plain,(
    ! [C_818,D_819,A_820] :
      ( k1_partfun1('#skF_1','#skF_1',C_818,D_819,'#skF_2',A_820) = k5_relat_1('#skF_2',A_820)
      | ~ v1_funct_1(A_820)
      | ~ r1_tarski(A_820,k2_zfmisc_1(C_818,D_819)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_11069])).

tff(c_11128,plain,(
    ! [A_821] :
      ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',A_821) = k5_relat_1('#skF_2',A_821)
      | ~ v1_funct_1(A_821)
      | ~ r1_tarski(A_821,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5261,c_11100])).

tff(c_11152,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8117,c_11128])).

tff(c_11185,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7658,c_11152])).

tff(c_7659,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7656,c_185])).

tff(c_11191,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11185,c_7659])).

tff(c_11198,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_11191])).

tff(c_11201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_90,c_6718,c_6193,c_7323,c_11198])).

tff(c_11203,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5280])).

tff(c_11202,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5280])).

tff(c_11355,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11203,c_11203,c_11202])).

tff(c_11356,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_11355])).

tff(c_11217,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11203,c_8])).

tff(c_11377,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11356,c_11217])).

tff(c_11429,plain,(
    ! [A_832,B_833,D_834] :
      ( r2_relset_1(A_832,B_833,D_834,D_834)
      | ~ m1_subset_1(D_834,k1_zfmisc_1(k2_zfmisc_1(A_832,B_833))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_11989,plain,(
    ! [A_903,B_904,A_905] :
      ( r2_relset_1(A_903,B_904,A_905,A_905)
      | ~ r1_tarski(A_905,k2_zfmisc_1(A_903,B_904)) ) ),
    inference(resolution,[status(thm)],[c_18,c_11429])).

tff(c_12002,plain,(
    ! [A_903,B_904] : r2_relset_1(A_903,B_904,'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_11377,c_11989])).

tff(c_11391,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11356,c_90])).

tff(c_11387,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11356,c_282])).

tff(c_124,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_130,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_24])).

tff(c_11216,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11203,c_11203,c_130])).

tff(c_11375,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11356,c_11356,c_11216])).

tff(c_11389,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11356,c_86])).

tff(c_11927,plain,(
    ! [C_889,A_890,B_891] :
      ( v2_funct_1(C_889)
      | ~ v3_funct_2(C_889,A_890,B_891)
      | ~ v1_funct_1(C_889)
      | ~ m1_subset_1(C_889,k1_zfmisc_1(k2_zfmisc_1(A_890,B_891))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_12199,plain,(
    ! [A_934] :
      ( v2_funct_1(k6_partfun1(A_934))
      | ~ v3_funct_2(k6_partfun1(A_934),A_934,A_934)
      | ~ v1_funct_1(k6_partfun1(A_934)) ) ),
    inference(resolution,[status(thm)],[c_74,c_11927])).

tff(c_12202,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11375,c_12199])).

tff(c_12204,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11391,c_11375,c_11389,c_11375,c_12202])).

tff(c_20,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_94,plain,(
    ! [A_8] : k1_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_20])).

tff(c_142,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_94])).

tff(c_11214,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11203,c_11203,c_142])).

tff(c_11373,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11356,c_11356,c_11214])).

tff(c_11385,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11356,c_11356,c_5271])).

tff(c_11212,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11203,c_11203,c_14])).

tff(c_11368,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11356,c_11356,c_11212])).

tff(c_11577,plain,(
    ! [A_840,B_841,C_842] :
      ( k1_relset_1(A_840,B_841,C_842) = k1_relat_1(C_842)
      | ~ m1_subset_1(C_842,k1_zfmisc_1(k2_zfmisc_1(A_840,B_841))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12076,plain,(
    ! [B_916,C_917] :
      ( k1_relset_1('#skF_1',B_916,C_917) = k1_relat_1(C_917)
      | ~ m1_subset_1(C_917,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11368,c_11577])).

tff(c_12078,plain,(
    ! [B_916] : k1_relset_1('#skF_1',B_916,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_11385,c_12076])).

tff(c_12083,plain,(
    ! [B_916] : k1_relset_1('#skF_1',B_916,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11373,c_12078])).

tff(c_11380,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11356,c_11203])).

tff(c_52,plain,(
    ! [C_28,B_27] :
      ( v1_funct_2(C_28,k1_xboole_0,B_27)
      | k1_relset_1(k1_xboole_0,B_27,C_28) != k1_xboole_0
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_95,plain,(
    ! [C_28,B_27] :
      ( v1_funct_2(C_28,k1_xboole_0,B_27)
      | k1_relset_1(k1_xboole_0,B_27,C_28) != k1_xboole_0
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_52])).

tff(c_11689,plain,(
    ! [C_852,B_853] :
      ( v1_funct_2(C_852,'#skF_1',B_853)
      | k1_relset_1('#skF_1',B_853,C_852) != '#skF_1'
      | ~ m1_subset_1(C_852,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11380,c_11380,c_11380,c_11380,c_95])).

tff(c_11695,plain,(
    ! [B_853] :
      ( v1_funct_2('#skF_1','#skF_1',B_853)
      | k1_relset_1('#skF_1',B_853,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_11385,c_11689])).

tff(c_12086,plain,(
    ! [B_853] : v1_funct_2('#skF_1','#skF_1',B_853) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12083,c_11695])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_11211,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11203,c_11203,c_12])).

tff(c_11502,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11356,c_11356,c_11211])).

tff(c_12308,plain,(
    ! [A_947,B_948] :
      ( k2_funct_2(A_947,B_948) = k2_funct_1(B_948)
      | ~ m1_subset_1(B_948,k1_zfmisc_1(k2_zfmisc_1(A_947,A_947)))
      | ~ v3_funct_2(B_948,A_947,A_947)
      | ~ v1_funct_2(B_948,A_947,A_947)
      | ~ v1_funct_1(B_948) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_12791,plain,(
    ! [B_1013] :
      ( k2_funct_2('#skF_1',B_1013) = k2_funct_1(B_1013)
      | ~ m1_subset_1(B_1013,k1_zfmisc_1('#skF_1'))
      | ~ v3_funct_2(B_1013,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_1013,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_1013) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11368,c_12308])).

tff(c_12794,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_11385,c_12791])).

tff(c_12801,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11391,c_12086,c_11389,c_12794])).

tff(c_12811,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12801,c_64])).

tff(c_12817,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11391,c_12086,c_11389,c_11385,c_11502,c_11502,c_12811])).

tff(c_12866,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_12817,c_16])).

tff(c_232,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_220])).

tff(c_11209,plain,(
    ! [A_3] :
      ( A_3 = '#skF_2'
      | ~ r1_tarski(A_3,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11203,c_11203,c_232])).

tff(c_11595,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11356,c_11356,c_11209])).

tff(c_12897,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12866,c_11595])).

tff(c_12919,plain,
    ( k6_partfun1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12897,c_91])).

tff(c_12925,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11387,c_11391,c_12204,c_11375,c_11373,c_12919])).

tff(c_12597,plain,(
    ! [D_991,B_994,F_992,A_990,E_993,C_995] :
      ( k1_partfun1(A_990,B_994,C_995,D_991,E_993,F_992) = k5_relat_1(E_993,F_992)
      | ~ m1_subset_1(F_992,k1_zfmisc_1(k2_zfmisc_1(C_995,D_991)))
      | ~ v1_funct_1(F_992)
      | ~ m1_subset_1(E_993,k1_zfmisc_1(k2_zfmisc_1(A_990,B_994)))
      | ~ v1_funct_1(E_993) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_13540,plain,(
    ! [A_1057,B_1058,A_1059,E_1060] :
      ( k1_partfun1(A_1057,B_1058,A_1059,A_1059,E_1060,k6_partfun1(A_1059)) = k5_relat_1(E_1060,k6_partfun1(A_1059))
      | ~ v1_funct_1(k6_partfun1(A_1059))
      | ~ m1_subset_1(E_1060,k1_zfmisc_1(k2_zfmisc_1(A_1057,B_1058)))
      | ~ v1_funct_1(E_1060) ) ),
    inference(resolution,[status(thm)],[c_74,c_12597])).

tff(c_13542,plain,(
    ! [A_1057,B_1058,E_1060] :
      ( k1_partfun1(A_1057,B_1058,'#skF_1','#skF_1',E_1060,k6_partfun1('#skF_1')) = k5_relat_1(E_1060,k6_partfun1('#skF_1'))
      | ~ v1_funct_1('#skF_1')
      | ~ m1_subset_1(E_1060,k1_zfmisc_1(k2_zfmisc_1(A_1057,B_1058)))
      | ~ v1_funct_1(E_1060) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11375,c_13540])).

tff(c_13545,plain,(
    ! [A_1061,B_1062,E_1063] :
      ( k1_partfun1(A_1061,B_1062,'#skF_1','#skF_1',E_1063,'#skF_1') = k5_relat_1(E_1063,'#skF_1')
      | ~ m1_subset_1(E_1063,k1_zfmisc_1(k2_zfmisc_1(A_1061,B_1062)))
      | ~ v1_funct_1(E_1063) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11391,c_11375,c_11375,c_13542])).

tff(c_13565,plain,(
    ! [A_1064] :
      ( k1_partfun1(A_1064,A_1064,'#skF_1','#skF_1',k6_partfun1(A_1064),'#skF_1') = k5_relat_1(k6_partfun1(A_1064),'#skF_1')
      | ~ v1_funct_1(k6_partfun1(A_1064)) ) ),
    inference(resolution,[status(thm)],[c_74,c_13545])).

tff(c_13567,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_1') = k5_relat_1(k6_partfun1('#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11375,c_13565])).

tff(c_13569,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11391,c_12925,c_11375,c_11375,c_13567])).

tff(c_11388,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11356,c_11356,c_185])).

tff(c_11622,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11375,c_11388])).

tff(c_12804,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12801,c_11622])).

tff(c_12903,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12897,c_12804])).

tff(c_13570,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13569,c_12903])).

tff(c_13573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12002,c_13570])).

tff(c_13574,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_11355])).

tff(c_13575,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_11355])).

tff(c_13605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13574,c_13575])).

tff(c_13606,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_15020,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15017,c_13606])).

tff(c_16157,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16089,c_15020])).

tff(c_16164,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_16157])).

tff(c_16167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13686,c_90,c_14410,c_13912,c_14293,c_16164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:55:50 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.77/4.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.05/4.20  
% 11.05/4.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.05/4.21  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 11.05/4.21  
% 11.05/4.21  %Foreground sorts:
% 11.05/4.21  
% 11.05/4.21  
% 11.05/4.21  %Background operators:
% 11.05/4.21  
% 11.05/4.21  
% 11.05/4.21  %Foreground operators:
% 11.05/4.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.05/4.21  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.05/4.21  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.05/4.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.05/4.21  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.05/4.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.05/4.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.05/4.21  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 11.05/4.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.05/4.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.05/4.21  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.05/4.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.05/4.21  tff('#skF_2', type, '#skF_2': $i).
% 11.05/4.21  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 11.05/4.21  tff('#skF_1', type, '#skF_1': $i).
% 11.05/4.21  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 11.05/4.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.05/4.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.05/4.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.05/4.21  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.05/4.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.05/4.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.05/4.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.05/4.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.05/4.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.05/4.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.05/4.21  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 11.05/4.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.05/4.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.05/4.21  
% 11.22/4.24  tff(f_173, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 11.22/4.24  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.22/4.24  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 11.22/4.24  tff(f_138, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 11.22/4.24  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 11.22/4.24  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.22/4.24  tff(f_118, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 11.22/4.24  tff(f_160, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.22/4.24  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 11.22/4.24  tff(f_158, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 11.22/4.24  tff(f_134, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 11.22/4.24  tff(f_148, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 11.22/4.24  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.22/4.24  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.22/4.24  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.22/4.24  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.22/4.24  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.22/4.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.22/4.24  tff(f_48, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 11.22/4.24  tff(f_47, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 11.22/4.24  tff(c_84, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.22/4.24  tff(c_13669, plain, (![C_1071, A_1072, B_1073]: (v1_relat_1(C_1071) | ~m1_subset_1(C_1071, k1_zfmisc_1(k2_zfmisc_1(A_1072, B_1073))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.22/4.24  tff(c_13686, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_13669])).
% 11.22/4.24  tff(c_90, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.22/4.24  tff(c_86, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.22/4.24  tff(c_14389, plain, (![C_1179, A_1180, B_1181]: (v2_funct_1(C_1179) | ~v3_funct_2(C_1179, A_1180, B_1181) | ~v1_funct_1(C_1179) | ~m1_subset_1(C_1179, k1_zfmisc_1(k2_zfmisc_1(A_1180, B_1181))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.22/4.24  tff(c_14399, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_14389])).
% 11.22/4.24  tff(c_14410, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_14399])).
% 11.22/4.24  tff(c_74, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.22/4.24  tff(c_13900, plain, (![A_1107, B_1108, D_1109]: (r2_relset_1(A_1107, B_1108, D_1109, D_1109) | ~m1_subset_1(D_1109, k1_zfmisc_1(k2_zfmisc_1(A_1107, B_1108))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.22/4.24  tff(c_13912, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_74, c_13900])).
% 11.22/4.24  tff(c_13769, plain, (![C_1083, B_1084, A_1085]: (v5_relat_1(C_1083, B_1084) | ~m1_subset_1(C_1083, k1_zfmisc_1(k2_zfmisc_1(A_1085, B_1084))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.22/4.24  tff(c_13788, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_13769])).
% 11.22/4.24  tff(c_13927, plain, (![B_1114, A_1115]: (k2_relat_1(B_1114)=A_1115 | ~v2_funct_2(B_1114, A_1115) | ~v5_relat_1(B_1114, A_1115) | ~v1_relat_1(B_1114))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.22/4.24  tff(c_13939, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_13788, c_13927])).
% 11.22/4.24  tff(c_13949, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13686, c_13939])).
% 11.22/4.24  tff(c_13957, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_13949])).
% 11.22/4.24  tff(c_14268, plain, (![C_1167, B_1168, A_1169]: (v2_funct_2(C_1167, B_1168) | ~v3_funct_2(C_1167, A_1169, B_1168) | ~v1_funct_1(C_1167) | ~m1_subset_1(C_1167, k1_zfmisc_1(k2_zfmisc_1(A_1169, B_1168))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.22/4.24  tff(c_14278, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_14268])).
% 11.22/4.24  tff(c_14290, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_14278])).
% 11.22/4.24  tff(c_14292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13957, c_14290])).
% 11.22/4.24  tff(c_14293, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_13949])).
% 11.22/4.24  tff(c_80, plain, (![A_42]: (k6_relat_1(A_42)=k6_partfun1(A_42))), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.22/4.24  tff(c_26, plain, (![A_9]: (k5_relat_1(k2_funct_1(A_9), A_9)=k6_relat_1(k2_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.22/4.24  tff(c_92, plain, (![A_9]: (k5_relat_1(k2_funct_1(A_9), A_9)=k6_partfun1(k2_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_26])).
% 11.22/4.24  tff(c_88, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.22/4.24  tff(c_14994, plain, (![A_1275, B_1276]: (k2_funct_2(A_1275, B_1276)=k2_funct_1(B_1276) | ~m1_subset_1(B_1276, k1_zfmisc_1(k2_zfmisc_1(A_1275, A_1275))) | ~v3_funct_2(B_1276, A_1275, A_1275) | ~v1_funct_2(B_1276, A_1275, A_1275) | ~v1_funct_1(B_1276))), inference(cnfTransformation, [status(thm)], [f_158])).
% 11.22/4.24  tff(c_15004, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_14994])).
% 11.22/4.24  tff(c_15017, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_15004])).
% 11.22/4.24  tff(c_14909, plain, (![A_1257, B_1258]: (v1_funct_1(k2_funct_2(A_1257, B_1258)) | ~m1_subset_1(B_1258, k1_zfmisc_1(k2_zfmisc_1(A_1257, A_1257))) | ~v3_funct_2(B_1258, A_1257, A_1257) | ~v1_funct_2(B_1258, A_1257, A_1257) | ~v1_funct_1(B_1258))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.22/4.24  tff(c_14919, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_14909])).
% 11.22/4.24  tff(c_14932, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_14919])).
% 11.22/4.24  tff(c_15018, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_15017, c_14932])).
% 11.22/4.24  tff(c_64, plain, (![A_31, B_32]: (m1_subset_1(k2_funct_2(A_31, B_32), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~v3_funct_2(B_32, A_31, A_31) | ~v1_funct_2(B_32, A_31, A_31) | ~v1_funct_1(B_32))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.22/4.24  tff(c_15427, plain, (![B_1309, E_1308, F_1307, C_1310, A_1305, D_1306]: (k1_partfun1(A_1305, B_1309, C_1310, D_1306, E_1308, F_1307)=k5_relat_1(E_1308, F_1307) | ~m1_subset_1(F_1307, k1_zfmisc_1(k2_zfmisc_1(C_1310, D_1306))) | ~v1_funct_1(F_1307) | ~m1_subset_1(E_1308, k1_zfmisc_1(k2_zfmisc_1(A_1305, B_1309))) | ~v1_funct_1(E_1308))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.22/4.24  tff(c_15438, plain, (![A_1305, B_1309, E_1308]: (k1_partfun1(A_1305, B_1309, '#skF_1', '#skF_1', E_1308, '#skF_2')=k5_relat_1(E_1308, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_1308, k1_zfmisc_1(k2_zfmisc_1(A_1305, B_1309))) | ~v1_funct_1(E_1308))), inference(resolution, [status(thm)], [c_84, c_15427])).
% 11.22/4.24  tff(c_15466, plain, (![A_1311, B_1312, E_1313]: (k1_partfun1(A_1311, B_1312, '#skF_1', '#skF_1', E_1313, '#skF_2')=k5_relat_1(E_1313, '#skF_2') | ~m1_subset_1(E_1313, k1_zfmisc_1(k2_zfmisc_1(A_1311, B_1312))) | ~v1_funct_1(E_1313))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_15438])).
% 11.22/4.24  tff(c_16053, plain, (![A_1327, B_1328]: (k1_partfun1(A_1327, A_1327, '#skF_1', '#skF_1', k2_funct_2(A_1327, B_1328), '#skF_2')=k5_relat_1(k2_funct_2(A_1327, B_1328), '#skF_2') | ~v1_funct_1(k2_funct_2(A_1327, B_1328)) | ~m1_subset_1(B_1328, k1_zfmisc_1(k2_zfmisc_1(A_1327, A_1327))) | ~v3_funct_2(B_1328, A_1327, A_1327) | ~v1_funct_2(B_1328, A_1327, A_1327) | ~v1_funct_1(B_1328))), inference(resolution, [status(thm)], [c_64, c_15466])).
% 11.22/4.24  tff(c_16068, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_16053])).
% 11.22/4.24  tff(c_16089, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_15018, c_15017, c_15017, c_15017, c_16068])).
% 11.22/4.24  tff(c_265, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.22/4.24  tff(c_282, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_265])).
% 11.22/4.24  tff(c_987, plain, (![C_173, A_174, B_175]: (v2_funct_1(C_173) | ~v3_funct_2(C_173, A_174, B_175) | ~v1_funct_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.22/4.24  tff(c_997, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_987])).
% 11.22/4.24  tff(c_1008, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_997])).
% 11.22/4.24  tff(c_452, plain, (![A_89, B_90, D_91]: (r2_relset_1(A_89, B_90, D_91, D_91) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.22/4.24  tff(c_464, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_74, c_452])).
% 11.22/4.24  tff(c_839, plain, (![A_150, B_151, C_152]: (k1_relset_1(A_150, B_151, C_152)=k1_relat_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.22/4.24  tff(c_859, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_839])).
% 11.22/4.24  tff(c_1346, plain, (![B_222, A_223, C_224]: (k1_xboole_0=B_222 | k1_relset_1(A_223, B_222, C_224)=A_223 | ~v1_funct_2(C_224, A_223, B_222) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_223, B_222))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.22/4.24  tff(c_1356, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_1346])).
% 11.22/4.24  tff(c_1368, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_859, c_1356])).
% 11.22/4.24  tff(c_1370, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_1368])).
% 11.22/4.24  tff(c_28, plain, (![A_9]: (k5_relat_1(A_9, k2_funct_1(A_9))=k6_relat_1(k1_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.22/4.24  tff(c_91, plain, (![A_9]: (k5_relat_1(A_9, k2_funct_1(A_9))=k6_partfun1(k1_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_28])).
% 11.22/4.24  tff(c_1535, plain, (![A_259, B_260]: (k2_funct_2(A_259, B_260)=k2_funct_1(B_260) | ~m1_subset_1(B_260, k1_zfmisc_1(k2_zfmisc_1(A_259, A_259))) | ~v3_funct_2(B_260, A_259, A_259) | ~v1_funct_2(B_260, A_259, A_259) | ~v1_funct_1(B_260))), inference(cnfTransformation, [status(thm)], [f_158])).
% 11.22/4.24  tff(c_1545, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_1535])).
% 11.22/4.24  tff(c_1558, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_1545])).
% 11.22/4.24  tff(c_1501, plain, (![A_253, B_254]: (v1_funct_1(k2_funct_2(A_253, B_254)) | ~m1_subset_1(B_254, k1_zfmisc_1(k2_zfmisc_1(A_253, A_253))) | ~v3_funct_2(B_254, A_253, A_253) | ~v1_funct_2(B_254, A_253, A_253) | ~v1_funct_1(B_254))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.22/4.24  tff(c_1511, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_1501])).
% 11.22/4.24  tff(c_1524, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_1511])).
% 11.22/4.24  tff(c_1559, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_1524])).
% 11.22/4.24  tff(c_1757, plain, (![A_281, B_282]: (m1_subset_1(k2_funct_2(A_281, B_282), k1_zfmisc_1(k2_zfmisc_1(A_281, A_281))) | ~m1_subset_1(B_282, k1_zfmisc_1(k2_zfmisc_1(A_281, A_281))) | ~v3_funct_2(B_282, A_281, A_281) | ~v1_funct_2(B_282, A_281, A_281) | ~v1_funct_1(B_282))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.22/4.24  tff(c_1799, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1558, c_1757])).
% 11.22/4.24  tff(c_1823, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_1799])).
% 11.22/4.24  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.22/4.24  tff(c_1893, plain, (r1_tarski(k2_funct_1('#skF_2'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1823, c_16])).
% 11.22/4.24  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.22/4.24  tff(c_1954, plain, (![C_288, D_284, E_286, A_283, F_285, B_287]: (k1_partfun1(A_283, B_287, C_288, D_284, E_286, F_285)=k5_relat_1(E_286, F_285) | ~m1_subset_1(F_285, k1_zfmisc_1(k2_zfmisc_1(C_288, D_284))) | ~v1_funct_1(F_285) | ~m1_subset_1(E_286, k1_zfmisc_1(k2_zfmisc_1(A_283, B_287))) | ~v1_funct_1(E_286))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.22/4.24  tff(c_4885, plain, (![C_379, A_380, A_381, B_378, E_377, D_382]: (k1_partfun1(A_381, B_378, C_379, D_382, E_377, A_380)=k5_relat_1(E_377, A_380) | ~v1_funct_1(A_380) | ~m1_subset_1(E_377, k1_zfmisc_1(k2_zfmisc_1(A_381, B_378))) | ~v1_funct_1(E_377) | ~r1_tarski(A_380, k2_zfmisc_1(C_379, D_382)))), inference(resolution, [status(thm)], [c_18, c_1954])).
% 11.22/4.24  tff(c_4910, plain, (![C_379, D_382, A_380]: (k1_partfun1('#skF_1', '#skF_1', C_379, D_382, '#skF_2', A_380)=k5_relat_1('#skF_2', A_380) | ~v1_funct_1(A_380) | ~v1_funct_1('#skF_2') | ~r1_tarski(A_380, k2_zfmisc_1(C_379, D_382)))), inference(resolution, [status(thm)], [c_84, c_4885])).
% 11.22/4.24  tff(c_4945, plain, (![C_383, D_384, A_385]: (k1_partfun1('#skF_1', '#skF_1', C_383, D_384, '#skF_2', A_385)=k5_relat_1('#skF_2', A_385) | ~v1_funct_1(A_385) | ~r1_tarski(A_385, k2_zfmisc_1(C_383, D_384)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_4910])).
% 11.22/4.24  tff(c_4972, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_1893, c_4945])).
% 11.22/4.24  tff(c_5017, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1559, c_4972])).
% 11.22/4.24  tff(c_82, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.22/4.24  tff(c_185, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_82])).
% 11.22/4.24  tff(c_1560, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_185])).
% 11.22/4.24  tff(c_5024, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5017, c_1560])).
% 11.22/4.24  tff(c_5031, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_91, c_5024])).
% 11.22/4.24  tff(c_5034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_282, c_90, c_1008, c_464, c_1370, c_5031])).
% 11.22/4.24  tff(c_5035, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1368])).
% 11.22/4.24  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.22/4.24  tff(c_5077, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_5035, c_8])).
% 11.22/4.24  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.22/4.24  tff(c_5072, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5035, c_5035, c_14])).
% 11.22/4.24  tff(c_186, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.22/4.24  tff(c_194, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_84, c_186])).
% 11.22/4.24  tff(c_220, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.22/4.24  tff(c_227, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_194, c_220])).
% 11.22/4.24  tff(c_347, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_227])).
% 11.22/4.24  tff(c_5255, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5072, c_347])).
% 11.22/4.24  tff(c_5260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5077, c_5255])).
% 11.22/4.24  tff(c_5261, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_227])).
% 11.22/4.24  tff(c_5271, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5261, c_84])).
% 11.22/4.24  tff(c_6597, plain, (![C_591, A_592, B_593]: (v2_funct_1(C_591) | ~v3_funct_2(C_591, A_592, B_593) | ~v1_funct_1(C_591) | ~m1_subset_1(C_591, k1_zfmisc_1(k2_zfmisc_1(A_592, B_593))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.22/4.24  tff(c_6704, plain, (![C_606]: (v2_funct_1(C_606) | ~v3_funct_2(C_606, '#skF_1', '#skF_1') | ~v1_funct_1(C_606) | ~m1_subset_1(C_606, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5261, c_6597])).
% 11.22/4.24  tff(c_6710, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_5271, c_6704])).
% 11.22/4.24  tff(c_6718, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_6710])).
% 11.22/4.24  tff(c_6181, plain, (![A_532, B_533, D_534]: (r2_relset_1(A_532, B_533, D_534, D_534) | ~m1_subset_1(D_534, k1_zfmisc_1(k2_zfmisc_1(A_532, B_533))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.22/4.24  tff(c_6193, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_74, c_6181])).
% 11.22/4.24  tff(c_6227, plain, (![A_537, B_538, C_539]: (k1_relset_1(A_537, B_538, C_539)=k1_relat_1(C_539) | ~m1_subset_1(C_539, k1_zfmisc_1(k2_zfmisc_1(A_537, B_538))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.22/4.24  tff(c_6289, plain, (![C_544]: (k1_relset_1('#skF_1', '#skF_1', C_544)=k1_relat_1(C_544) | ~m1_subset_1(C_544, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5261, c_6227])).
% 11.22/4.24  tff(c_6302, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_5271, c_6289])).
% 11.22/4.24  tff(c_6843, plain, (![B_634, C_635, A_636]: (k1_xboole_0=B_634 | v1_funct_2(C_635, A_636, B_634) | k1_relset_1(A_636, B_634, C_635)!=A_636 | ~m1_subset_1(C_635, k1_zfmisc_1(k2_zfmisc_1(A_636, B_634))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.22/4.24  tff(c_6846, plain, (![C_635]: (k1_xboole_0='#skF_1' | v1_funct_2(C_635, '#skF_1', '#skF_1') | k1_relset_1('#skF_1', '#skF_1', C_635)!='#skF_1' | ~m1_subset_1(C_635, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5261, c_6843])).
% 11.22/4.24  tff(c_6913, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_6846])).
% 11.22/4.24  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.22/4.24  tff(c_5280, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_5261, c_10])).
% 11.22/4.24  tff(c_5364, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_5280])).
% 11.22/4.24  tff(c_6951, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6913, c_5364])).
% 11.22/4.24  tff(c_6959, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6913, c_6913, c_14])).
% 11.22/4.24  tff(c_7189, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6959, c_5261])).
% 11.22/4.24  tff(c_7191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6951, c_7189])).
% 11.22/4.24  tff(c_7193, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_6846])).
% 11.22/4.24  tff(c_7257, plain, (![B_662, A_663, C_664]: (k1_xboole_0=B_662 | k1_relset_1(A_663, B_662, C_664)=A_663 | ~v1_funct_2(C_664, A_663, B_662) | ~m1_subset_1(C_664, k1_zfmisc_1(k2_zfmisc_1(A_663, B_662))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.22/4.24  tff(c_7260, plain, (![C_664]: (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', C_664)='#skF_1' | ~v1_funct_2(C_664, '#skF_1', '#skF_1') | ~m1_subset_1(C_664, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5261, c_7257])).
% 11.22/4.24  tff(c_7307, plain, (![C_667]: (k1_relset_1('#skF_1', '#skF_1', C_667)='#skF_1' | ~v1_funct_2(C_667, '#skF_1', '#skF_1') | ~m1_subset_1(C_667, k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_7193, c_7260])).
% 11.22/4.24  tff(c_7313, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_5271, c_7307])).
% 11.22/4.24  tff(c_7323, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_6302, c_7313])).
% 11.22/4.24  tff(c_7606, plain, (![A_689, B_690]: (k2_funct_2(A_689, B_690)=k2_funct_1(B_690) | ~m1_subset_1(B_690, k1_zfmisc_1(k2_zfmisc_1(A_689, A_689))) | ~v3_funct_2(B_690, A_689, A_689) | ~v1_funct_2(B_690, A_689, A_689) | ~v1_funct_1(B_690))), inference(cnfTransformation, [status(thm)], [f_158])).
% 11.22/4.24  tff(c_7640, plain, (![B_693]: (k2_funct_2('#skF_1', B_693)=k2_funct_1(B_693) | ~m1_subset_1(B_693, k1_zfmisc_1('#skF_2')) | ~v3_funct_2(B_693, '#skF_1', '#skF_1') | ~v1_funct_2(B_693, '#skF_1', '#skF_1') | ~v1_funct_1(B_693))), inference(superposition, [status(thm), theory('equality')], [c_5261, c_7606])).
% 11.22/4.24  tff(c_7646, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_5271, c_7640])).
% 11.22/4.24  tff(c_7656, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_7646])).
% 11.22/4.24  tff(c_7547, plain, (![A_682, B_683]: (v1_funct_1(k2_funct_2(A_682, B_683)) | ~m1_subset_1(B_683, k1_zfmisc_1(k2_zfmisc_1(A_682, A_682))) | ~v3_funct_2(B_683, A_682, A_682) | ~v1_funct_2(B_683, A_682, A_682) | ~v1_funct_1(B_683))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.22/4.24  tff(c_7585, plain, (![B_686]: (v1_funct_1(k2_funct_2('#skF_1', B_686)) | ~m1_subset_1(B_686, k1_zfmisc_1('#skF_2')) | ~v3_funct_2(B_686, '#skF_1', '#skF_1') | ~v1_funct_2(B_686, '#skF_1', '#skF_1') | ~v1_funct_1(B_686))), inference(superposition, [status(thm), theory('equality')], [c_5261, c_7547])).
% 11.22/4.24  tff(c_7591, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_5271, c_7585])).
% 11.22/4.24  tff(c_7601, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_7591])).
% 11.22/4.24  tff(c_7658, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7656, c_7601])).
% 11.22/4.24  tff(c_7677, plain, (![A_695, B_696]: (v3_funct_2(k2_funct_2(A_695, B_696), A_695, A_695) | ~m1_subset_1(B_696, k1_zfmisc_1(k2_zfmisc_1(A_695, A_695))) | ~v3_funct_2(B_696, A_695, A_695) | ~v1_funct_2(B_696, A_695, A_695) | ~v1_funct_1(B_696))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.22/4.24  tff(c_7745, plain, (![B_701]: (v3_funct_2(k2_funct_2('#skF_1', B_701), '#skF_1', '#skF_1') | ~m1_subset_1(B_701, k1_zfmisc_1('#skF_2')) | ~v3_funct_2(B_701, '#skF_1', '#skF_1') | ~v1_funct_2(B_701, '#skF_1', '#skF_1') | ~v1_funct_1(B_701))), inference(superposition, [status(thm), theory('equality')], [c_5261, c_7677])).
% 11.22/4.24  tff(c_7757, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7656, c_7745])).
% 11.22/4.24  tff(c_7762, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_5271, c_7757])).
% 11.22/4.24  tff(c_6719, plain, (![A_6]: (v2_funct_1(A_6) | ~v3_funct_2(A_6, '#skF_1', '#skF_1') | ~v1_funct_1(A_6) | ~r1_tarski(A_6, '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_6704])).
% 11.22/4.24  tff(c_7771, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~r1_tarski(k2_funct_1('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_7762, c_6719])).
% 11.22/4.24  tff(c_7780, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~r1_tarski(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7658, c_7771])).
% 11.22/4.24  tff(c_7781, plain, (~r1_tarski(k2_funct_1('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_7780])).
% 11.22/4.24  tff(c_7982, plain, (![A_710, B_711]: (m1_subset_1(k2_funct_2(A_710, B_711), k1_zfmisc_1(k2_zfmisc_1(A_710, A_710))) | ~m1_subset_1(B_711, k1_zfmisc_1(k2_zfmisc_1(A_710, A_710))) | ~v3_funct_2(B_711, A_710, A_710) | ~v1_funct_2(B_711, A_710, A_710) | ~v1_funct_1(B_711))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.22/4.24  tff(c_8024, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7656, c_7982])).
% 11.22/4.24  tff(c_8051, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_5271, c_5261, c_5261, c_8024])).
% 11.22/4.24  tff(c_8089, plain, (r1_tarski(k2_funct_1('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_8051, c_16])).
% 11.22/4.24  tff(c_8115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7781, c_8089])).
% 11.22/4.24  tff(c_8117, plain, (r1_tarski(k2_funct_1('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_7780])).
% 11.22/4.24  tff(c_8462, plain, (![D_719, C_723, A_718, B_722, F_720, E_721]: (k1_partfun1(A_718, B_722, C_723, D_719, E_721, F_720)=k5_relat_1(E_721, F_720) | ~m1_subset_1(F_720, k1_zfmisc_1(k2_zfmisc_1(C_723, D_719))) | ~v1_funct_1(F_720) | ~m1_subset_1(E_721, k1_zfmisc_1(k2_zfmisc_1(A_718, B_722))) | ~v1_funct_1(E_721))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.22/4.24  tff(c_11032, plain, (![A_812, E_811, A_808, B_809, C_813, D_810]: (k1_partfun1(A_808, B_809, C_813, D_810, E_811, A_812)=k5_relat_1(E_811, A_812) | ~v1_funct_1(A_812) | ~m1_subset_1(E_811, k1_zfmisc_1(k2_zfmisc_1(A_808, B_809))) | ~v1_funct_1(E_811) | ~r1_tarski(A_812, k2_zfmisc_1(C_813, D_810)))), inference(resolution, [status(thm)], [c_18, c_8462])).
% 11.22/4.24  tff(c_11049, plain, (![C_814, D_815, E_816, A_817]: (k1_partfun1('#skF_1', '#skF_1', C_814, D_815, E_816, A_817)=k5_relat_1(E_816, A_817) | ~v1_funct_1(A_817) | ~m1_subset_1(E_816, k1_zfmisc_1('#skF_2')) | ~v1_funct_1(E_816) | ~r1_tarski(A_817, k2_zfmisc_1(C_814, D_815)))), inference(superposition, [status(thm), theory('equality')], [c_5261, c_11032])).
% 11.22/4.24  tff(c_11069, plain, (![C_814, D_815, A_817]: (k1_partfun1('#skF_1', '#skF_1', C_814, D_815, '#skF_2', A_817)=k5_relat_1('#skF_2', A_817) | ~v1_funct_1(A_817) | ~v1_funct_1('#skF_2') | ~r1_tarski(A_817, k2_zfmisc_1(C_814, D_815)))), inference(resolution, [status(thm)], [c_5271, c_11049])).
% 11.22/4.24  tff(c_11100, plain, (![C_818, D_819, A_820]: (k1_partfun1('#skF_1', '#skF_1', C_818, D_819, '#skF_2', A_820)=k5_relat_1('#skF_2', A_820) | ~v1_funct_1(A_820) | ~r1_tarski(A_820, k2_zfmisc_1(C_818, D_819)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_11069])).
% 11.22/4.24  tff(c_11128, plain, (![A_821]: (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', A_821)=k5_relat_1('#skF_2', A_821) | ~v1_funct_1(A_821) | ~r1_tarski(A_821, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5261, c_11100])).
% 11.22/4.24  tff(c_11152, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_8117, c_11128])).
% 11.22/4.24  tff(c_11185, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7658, c_11152])).
% 11.22/4.24  tff(c_7659, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7656, c_185])).
% 11.22/4.24  tff(c_11191, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11185, c_7659])).
% 11.22/4.24  tff(c_11198, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_91, c_11191])).
% 11.22/4.24  tff(c_11201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_282, c_90, c_6718, c_6193, c_7323, c_11198])).
% 11.22/4.24  tff(c_11203, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_5280])).
% 11.22/4.24  tff(c_11202, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_5280])).
% 11.22/4.24  tff(c_11355, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11203, c_11203, c_11202])).
% 11.22/4.24  tff(c_11356, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_11355])).
% 11.22/4.24  tff(c_11217, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_11203, c_8])).
% 11.22/4.24  tff(c_11377, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_11356, c_11217])).
% 11.22/4.24  tff(c_11429, plain, (![A_832, B_833, D_834]: (r2_relset_1(A_832, B_833, D_834, D_834) | ~m1_subset_1(D_834, k1_zfmisc_1(k2_zfmisc_1(A_832, B_833))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.22/4.24  tff(c_11989, plain, (![A_903, B_904, A_905]: (r2_relset_1(A_903, B_904, A_905, A_905) | ~r1_tarski(A_905, k2_zfmisc_1(A_903, B_904)))), inference(resolution, [status(thm)], [c_18, c_11429])).
% 11.22/4.24  tff(c_12002, plain, (![A_903, B_904]: (r2_relset_1(A_903, B_904, '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_11377, c_11989])).
% 11.22/4.24  tff(c_11391, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11356, c_90])).
% 11.22/4.24  tff(c_11387, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11356, c_282])).
% 11.22/4.24  tff(c_124, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.22/4.24  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.22/4.24  tff(c_130, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_124, c_24])).
% 11.22/4.24  tff(c_11216, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11203, c_11203, c_130])).
% 11.22/4.24  tff(c_11375, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11356, c_11356, c_11216])).
% 11.22/4.24  tff(c_11389, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11356, c_86])).
% 11.22/4.24  tff(c_11927, plain, (![C_889, A_890, B_891]: (v2_funct_1(C_889) | ~v3_funct_2(C_889, A_890, B_891) | ~v1_funct_1(C_889) | ~m1_subset_1(C_889, k1_zfmisc_1(k2_zfmisc_1(A_890, B_891))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.22/4.24  tff(c_12199, plain, (![A_934]: (v2_funct_1(k6_partfun1(A_934)) | ~v3_funct_2(k6_partfun1(A_934), A_934, A_934) | ~v1_funct_1(k6_partfun1(A_934)))), inference(resolution, [status(thm)], [c_74, c_11927])).
% 11.22/4.24  tff(c_12202, plain, (v2_funct_1(k6_partfun1('#skF_1')) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11375, c_12199])).
% 11.22/4.24  tff(c_12204, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11391, c_11375, c_11389, c_11375, c_12202])).
% 11.22/4.24  tff(c_20, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.22/4.24  tff(c_94, plain, (![A_8]: (k1_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_20])).
% 11.22/4.24  tff(c_142, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_130, c_94])).
% 11.22/4.24  tff(c_11214, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11203, c_11203, c_142])).
% 11.22/4.24  tff(c_11373, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11356, c_11356, c_11214])).
% 11.22/4.24  tff(c_11385, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11356, c_11356, c_5271])).
% 11.22/4.24  tff(c_11212, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11203, c_11203, c_14])).
% 11.22/4.24  tff(c_11368, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11356, c_11356, c_11212])).
% 11.22/4.24  tff(c_11577, plain, (![A_840, B_841, C_842]: (k1_relset_1(A_840, B_841, C_842)=k1_relat_1(C_842) | ~m1_subset_1(C_842, k1_zfmisc_1(k2_zfmisc_1(A_840, B_841))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.22/4.24  tff(c_12076, plain, (![B_916, C_917]: (k1_relset_1('#skF_1', B_916, C_917)=k1_relat_1(C_917) | ~m1_subset_1(C_917, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_11368, c_11577])).
% 11.22/4.24  tff(c_12078, plain, (![B_916]: (k1_relset_1('#skF_1', B_916, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_11385, c_12076])).
% 11.22/4.24  tff(c_12083, plain, (![B_916]: (k1_relset_1('#skF_1', B_916, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11373, c_12078])).
% 11.22/4.24  tff(c_11380, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11356, c_11203])).
% 11.22/4.24  tff(c_52, plain, (![C_28, B_27]: (v1_funct_2(C_28, k1_xboole_0, B_27) | k1_relset_1(k1_xboole_0, B_27, C_28)!=k1_xboole_0 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_27))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.22/4.24  tff(c_95, plain, (![C_28, B_27]: (v1_funct_2(C_28, k1_xboole_0, B_27) | k1_relset_1(k1_xboole_0, B_27, C_28)!=k1_xboole_0 | ~m1_subset_1(C_28, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_52])).
% 11.22/4.24  tff(c_11689, plain, (![C_852, B_853]: (v1_funct_2(C_852, '#skF_1', B_853) | k1_relset_1('#skF_1', B_853, C_852)!='#skF_1' | ~m1_subset_1(C_852, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_11380, c_11380, c_11380, c_11380, c_95])).
% 11.22/4.24  tff(c_11695, plain, (![B_853]: (v1_funct_2('#skF_1', '#skF_1', B_853) | k1_relset_1('#skF_1', B_853, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_11385, c_11689])).
% 11.22/4.24  tff(c_12086, plain, (![B_853]: (v1_funct_2('#skF_1', '#skF_1', B_853))), inference(demodulation, [status(thm), theory('equality')], [c_12083, c_11695])).
% 11.22/4.24  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.22/4.24  tff(c_11211, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11203, c_11203, c_12])).
% 11.22/4.24  tff(c_11502, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11356, c_11356, c_11211])).
% 11.22/4.24  tff(c_12308, plain, (![A_947, B_948]: (k2_funct_2(A_947, B_948)=k2_funct_1(B_948) | ~m1_subset_1(B_948, k1_zfmisc_1(k2_zfmisc_1(A_947, A_947))) | ~v3_funct_2(B_948, A_947, A_947) | ~v1_funct_2(B_948, A_947, A_947) | ~v1_funct_1(B_948))), inference(cnfTransformation, [status(thm)], [f_158])).
% 11.22/4.24  tff(c_12791, plain, (![B_1013]: (k2_funct_2('#skF_1', B_1013)=k2_funct_1(B_1013) | ~m1_subset_1(B_1013, k1_zfmisc_1('#skF_1')) | ~v3_funct_2(B_1013, '#skF_1', '#skF_1') | ~v1_funct_2(B_1013, '#skF_1', '#skF_1') | ~v1_funct_1(B_1013))), inference(superposition, [status(thm), theory('equality')], [c_11368, c_12308])).
% 11.22/4.24  tff(c_12794, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_11385, c_12791])).
% 11.22/4.24  tff(c_12801, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11391, c_12086, c_11389, c_12794])).
% 11.22/4.24  tff(c_12811, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12801, c_64])).
% 11.22/4.24  tff(c_12817, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11391, c_12086, c_11389, c_11385, c_11502, c_11502, c_12811])).
% 11.22/4.24  tff(c_12866, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_12817, c_16])).
% 11.22/4.24  tff(c_232, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_220])).
% 11.22/4.24  tff(c_11209, plain, (![A_3]: (A_3='#skF_2' | ~r1_tarski(A_3, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_11203, c_11203, c_232])).
% 11.22/4.24  tff(c_11595, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11356, c_11356, c_11209])).
% 11.22/4.24  tff(c_12897, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_12866, c_11595])).
% 11.22/4.24  tff(c_12919, plain, (k6_partfun1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12897, c_91])).
% 11.22/4.24  tff(c_12925, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11387, c_11391, c_12204, c_11375, c_11373, c_12919])).
% 11.22/4.24  tff(c_12597, plain, (![D_991, B_994, F_992, A_990, E_993, C_995]: (k1_partfun1(A_990, B_994, C_995, D_991, E_993, F_992)=k5_relat_1(E_993, F_992) | ~m1_subset_1(F_992, k1_zfmisc_1(k2_zfmisc_1(C_995, D_991))) | ~v1_funct_1(F_992) | ~m1_subset_1(E_993, k1_zfmisc_1(k2_zfmisc_1(A_990, B_994))) | ~v1_funct_1(E_993))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.22/4.24  tff(c_13540, plain, (![A_1057, B_1058, A_1059, E_1060]: (k1_partfun1(A_1057, B_1058, A_1059, A_1059, E_1060, k6_partfun1(A_1059))=k5_relat_1(E_1060, k6_partfun1(A_1059)) | ~v1_funct_1(k6_partfun1(A_1059)) | ~m1_subset_1(E_1060, k1_zfmisc_1(k2_zfmisc_1(A_1057, B_1058))) | ~v1_funct_1(E_1060))), inference(resolution, [status(thm)], [c_74, c_12597])).
% 11.22/4.24  tff(c_13542, plain, (![A_1057, B_1058, E_1060]: (k1_partfun1(A_1057, B_1058, '#skF_1', '#skF_1', E_1060, k6_partfun1('#skF_1'))=k5_relat_1(E_1060, k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_1') | ~m1_subset_1(E_1060, k1_zfmisc_1(k2_zfmisc_1(A_1057, B_1058))) | ~v1_funct_1(E_1060))), inference(superposition, [status(thm), theory('equality')], [c_11375, c_13540])).
% 11.22/4.24  tff(c_13545, plain, (![A_1061, B_1062, E_1063]: (k1_partfun1(A_1061, B_1062, '#skF_1', '#skF_1', E_1063, '#skF_1')=k5_relat_1(E_1063, '#skF_1') | ~m1_subset_1(E_1063, k1_zfmisc_1(k2_zfmisc_1(A_1061, B_1062))) | ~v1_funct_1(E_1063))), inference(demodulation, [status(thm), theory('equality')], [c_11391, c_11375, c_11375, c_13542])).
% 11.22/4.24  tff(c_13565, plain, (![A_1064]: (k1_partfun1(A_1064, A_1064, '#skF_1', '#skF_1', k6_partfun1(A_1064), '#skF_1')=k5_relat_1(k6_partfun1(A_1064), '#skF_1') | ~v1_funct_1(k6_partfun1(A_1064)))), inference(resolution, [status(thm)], [c_74, c_13545])).
% 11.22/4.24  tff(c_13567, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_1')=k5_relat_1(k6_partfun1('#skF_1'), '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11375, c_13565])).
% 11.22/4.24  tff(c_13569, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11391, c_12925, c_11375, c_11375, c_13567])).
% 11.22/4.24  tff(c_11388, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11356, c_11356, c_185])).
% 11.22/4.24  tff(c_11622, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11375, c_11388])).
% 11.22/4.24  tff(c_12804, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12801, c_11622])).
% 11.22/4.24  tff(c_12903, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12897, c_12804])).
% 11.22/4.24  tff(c_13570, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13569, c_12903])).
% 11.22/4.24  tff(c_13573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12002, c_13570])).
% 11.22/4.24  tff(c_13574, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_11355])).
% 11.22/4.24  tff(c_13575, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_11355])).
% 11.22/4.24  tff(c_13605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13574, c_13575])).
% 11.22/4.24  tff(c_13606, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_82])).
% 11.22/4.24  tff(c_15020, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_15017, c_13606])).
% 11.22/4.24  tff(c_16157, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_16089, c_15020])).
% 11.22/4.24  tff(c_16164, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_92, c_16157])).
% 11.22/4.24  tff(c_16167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13686, c_90, c_14410, c_13912, c_14293, c_16164])).
% 11.22/4.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.22/4.24  
% 11.22/4.24  Inference rules
% 11.22/4.24  ----------------------
% 11.22/4.24  #Ref     : 0
% 11.22/4.24  #Sup     : 3369
% 11.22/4.24  #Fact    : 0
% 11.22/4.24  #Define  : 0
% 11.22/4.24  #Split   : 45
% 11.22/4.24  #Chain   : 0
% 11.22/4.24  #Close   : 0
% 11.22/4.24  
% 11.22/4.24  Ordering : KBO
% 11.22/4.24  
% 11.22/4.24  Simplification rules
% 11.22/4.24  ----------------------
% 11.22/4.24  #Subsume      : 433
% 11.22/4.24  #Demod        : 4988
% 11.22/4.24  #Tautology    : 1571
% 11.22/4.24  #SimpNegUnit  : 19
% 11.22/4.24  #BackRed      : 237
% 11.22/4.24  
% 11.22/4.24  #Partial instantiations: 0
% 11.22/4.24  #Strategies tried      : 1
% 11.22/4.24  
% 11.22/4.24  Timing (in seconds)
% 11.22/4.24  ----------------------
% 11.22/4.24  Preprocessing        : 0.41
% 11.22/4.24  Parsing              : 0.21
% 11.22/4.24  CNF conversion       : 0.03
% 11.22/4.24  Main loop            : 2.98
% 11.22/4.24  Inferencing          : 0.92
% 11.22/4.24  Reduction            : 1.21
% 11.22/4.24  Demodulation         : 0.92
% 11.22/4.24  BG Simplification    : 0.07
% 11.22/4.25  Subsumption          : 0.56
% 11.22/4.25  Abstraction          : 0.11
% 11.22/4.25  MUC search           : 0.00
% 11.22/4.25  Cooper               : 0.00
% 11.22/4.25  Total                : 3.49
% 11.22/4.25  Index Insertion      : 0.00
% 11.22/4.25  Index Deletion       : 0.00
% 11.22/4.25  Index Matching       : 0.00
% 11.22/4.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
