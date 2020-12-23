%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:40 EST 2020

% Result     : Theorem 9.89s
% Output     : CNFRefutation 10.15s
% Verified   : 
% Statistics : Number of formulae       :  328 (2855 expanded)
%              Number of leaves         :   45 ( 870 expanded)
%              Depth                    :   16
%              Number of atoms          :  596 (6717 expanded)
%              Number of equality atoms :   93 (1657 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_163,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_137,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_68,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_154,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_106,plain,(
    r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_888,plain,(
    ! [A_159,B_160,D_161] :
      ( '#skF_5'(A_159,B_160,k1_funct_2(A_159,B_160),D_161) = D_161
      | ~ r2_hidden(D_161,k1_funct_2(A_159,B_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_895,plain,(
    '#skF_5'('#skF_7','#skF_8',k1_funct_2('#skF_7','#skF_8'),'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_106,c_888])).

tff(c_938,plain,(
    ! [A_164,B_165,D_166] :
      ( v1_relat_1('#skF_5'(A_164,B_165,k1_funct_2(A_164,B_165),D_166))
      | ~ r2_hidden(D_166,k1_funct_2(A_164,B_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_941,plain,
    ( v1_relat_1('#skF_9')
    | ~ r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_895,c_938])).

tff(c_943,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_941])).

tff(c_1106,plain,(
    ! [A_178,B_179,D_180] :
      ( k1_relat_1('#skF_5'(A_178,B_179,k1_funct_2(A_178,B_179),D_180)) = A_178
      | ~ r2_hidden(D_180,k1_funct_2(A_178,B_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1145,plain,
    ( k1_relat_1('#skF_9') = '#skF_7'
    | ~ r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_895,c_1106])).

tff(c_1149,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1145])).

tff(c_1360,plain,(
    ! [A_194,B_195,D_196] :
      ( r1_tarski(k2_relat_1('#skF_5'(A_194,B_195,k1_funct_2(A_194,B_195),D_196)),B_195)
      | ~ r2_hidden(D_196,k1_funct_2(A_194,B_195)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1393,plain,
    ( r1_tarski(k2_relat_1('#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_895,c_1360])).

tff(c_1403,plain,(
    r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1393])).

tff(c_2384,plain,(
    ! [C_260,A_261,B_262] :
      ( m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ r1_tarski(k2_relat_1(C_260),B_262)
      | ~ r1_tarski(k1_relat_1(C_260),A_261)
      | ~ v1_relat_1(C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_104,plain,
    ( ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_201,plain,(
    ~ v1_funct_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_512,plain,(
    ! [A_117,B_118,D_119] :
      ( '#skF_5'(A_117,B_118,k1_funct_2(A_117,B_118),D_119) = D_119
      | ~ r2_hidden(D_119,k1_funct_2(A_117,B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_519,plain,(
    '#skF_5'('#skF_7','#skF_8',k1_funct_2('#skF_7','#skF_8'),'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_106,c_512])).

tff(c_602,plain,(
    ! [A_124,B_125,D_126] :
      ( v1_funct_1('#skF_5'(A_124,B_125,k1_funct_2(A_124,B_125),D_126))
      | ~ r2_hidden(D_126,k1_funct_2(A_124,B_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_605,plain,
    ( v1_funct_1('#skF_9')
    | ~ r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_602])).

tff(c_607,plain,(
    v1_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_605])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_607])).

tff(c_610,plain,
    ( ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_619,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_610])).

tff(c_2393,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8')
    | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_2384,c_619])).

tff(c_2420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_14,c_1149,c_1403,c_2393])).

tff(c_2422,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_36,plain,(
    ! [C_19,A_17,B_18] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2429,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_2422,c_36])).

tff(c_9799,plain,(
    ! [A_742,B_743,D_744] :
      ( '#skF_5'(A_742,B_743,k1_funct_2(A_742,B_743),D_744) = D_744
      | ~ r2_hidden(D_744,k1_funct_2(A_742,B_743)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_9806,plain,(
    '#skF_5'('#skF_7','#skF_8',k1_funct_2('#skF_7','#skF_8'),'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_106,c_9799])).

tff(c_10019,plain,(
    ! [A_762,B_763,D_764] :
      ( k1_relat_1('#skF_5'(A_762,B_763,k1_funct_2(A_762,B_763),D_764)) = A_762
      | ~ r2_hidden(D_764,k1_funct_2(A_762,B_763)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_10058,plain,
    ( k1_relat_1('#skF_9') = '#skF_7'
    | ~ r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9806,c_10019])).

tff(c_10062,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_10058])).

tff(c_611,plain,(
    v1_funct_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_86,plain,(
    ! [A_54] :
      ( m1_subset_1(A_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_54),k2_relat_1(A_54))))
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_10090,plain,
    ( m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k2_relat_1('#skF_9'))))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_10062,c_86])).

tff(c_10113,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k2_relat_1('#skF_9')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_611,c_10090])).

tff(c_38,plain,(
    ! [C_23,B_21,A_20] :
      ( v1_xboole_0(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(B_21,A_20)))
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_11476,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_10113,c_38])).

tff(c_11482,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_11476])).

tff(c_2421,plain,(
    ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_11585,plain,(
    ! [C_853,A_854,B_855] :
      ( v1_funct_2(C_853,A_854,B_855)
      | ~ v1_partfun1(C_853,A_854)
      | ~ v1_funct_1(C_853)
      | ~ m1_subset_1(C_853,k1_zfmisc_1(k2_zfmisc_1(A_854,B_855))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_11603,plain,
    ( v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_partfun1('#skF_9','#skF_7')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_2422,c_11585])).

tff(c_11620,plain,
    ( v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_partfun1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_11603])).

tff(c_11621,plain,(
    ~ v1_partfun1('#skF_9','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_2421,c_11620])).

tff(c_88,plain,(
    ! [A_54] :
      ( v1_funct_2(A_54,k1_relat_1(A_54),k2_relat_1(A_54))
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_10093,plain,
    ( v1_funct_2('#skF_9','#skF_7',k2_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_10062,c_88])).

tff(c_10115,plain,(
    v1_funct_2('#skF_9','#skF_7',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_611,c_10093])).

tff(c_13079,plain,(
    ! [C_950,A_951,B_952] :
      ( v1_partfun1(C_950,A_951)
      | ~ v1_funct_2(C_950,A_951,B_952)
      | ~ v1_funct_1(C_950)
      | ~ m1_subset_1(C_950,k1_zfmisc_1(k2_zfmisc_1(A_951,B_952)))
      | v1_xboole_0(B_952) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_13085,plain,
    ( v1_partfun1('#skF_9','#skF_7')
    | ~ v1_funct_2('#skF_9','#skF_7',k2_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_10113,c_13079])).

tff(c_13114,plain,
    ( v1_partfun1('#skF_9','#skF_7')
    | v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_10115,c_13085])).

tff(c_13116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11482,c_11621,c_13114])).

tff(c_13117,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_11476])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_13125,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_13117,c_8])).

tff(c_118,plain,(
    ! [B_62] : k2_zfmisc_1(k1_xboole_0,B_62) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_122,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_26])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_9640,plain,(
    ! [A_723,B_724] :
      ( r1_tarski(k1_relat_1(A_723),k1_relat_1(B_724))
      | ~ r1_tarski(A_723,B_724)
      | ~ v1_relat_1(B_724)
      | ~ v1_relat_1(A_723) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_9648,plain,(
    ! [A_723] :
      ( r1_tarski(k1_relat_1(A_723),k1_xboole_0)
      | ~ r1_tarski(A_723,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_723) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_9640])).

tff(c_9843,plain,(
    ! [A_750] :
      ( r1_tarski(k1_relat_1(A_750),k1_xboole_0)
      | ~ r1_tarski(A_750,k1_xboole_0)
      | ~ v1_relat_1(A_750) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_9648])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_185,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_195,plain,(
    ! [C_79] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_185])).

tff(c_200,plain,(
    ! [A_10] :
      ( v1_relat_1(A_10)
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_195])).

tff(c_9860,plain,(
    ! [A_750] :
      ( v1_relat_1(k1_relat_1(A_750))
      | ~ r1_tarski(A_750,k1_xboole_0)
      | ~ v1_relat_1(A_750) ) ),
    inference(resolution,[status(thm)],[c_9843,c_200])).

tff(c_10072,plain,
    ( v1_relat_1('#skF_7')
    | ~ r1_tarski('#skF_9',k1_xboole_0)
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_10062,c_9860])).

tff(c_10101,plain,
    ( v1_relat_1('#skF_7')
    | ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_10072])).

tff(c_10117,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_10101])).

tff(c_13129,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13125,c_10117])).

tff(c_13164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_13129])).

tff(c_13166,plain,(
    r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_10101])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9549,plain,(
    ! [C_714,B_715,A_716] :
      ( v1_xboole_0(C_714)
      | ~ m1_subset_1(C_714,k1_zfmisc_1(k2_zfmisc_1(B_715,A_716)))
      | ~ v1_xboole_0(A_716) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_9559,plain,(
    ! [C_714] :
      ( v1_xboole_0(C_714)
      | ~ m1_subset_1(C_714,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_9549])).

tff(c_9582,plain,(
    ! [C_719] :
      ( v1_xboole_0(C_719)
      | ~ m1_subset_1(C_719,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9559])).

tff(c_9587,plain,(
    ! [A_10] :
      ( v1_xboole_0(A_10)
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_9582])).

tff(c_9864,plain,(
    ! [A_751] :
      ( v1_xboole_0(k1_relat_1(A_751))
      | ~ r1_tarski(A_751,k1_xboole_0)
      | ~ v1_relat_1(A_751) ) ),
    inference(resolution,[status(thm)],[c_9843,c_9587])).

tff(c_9874,plain,(
    ! [A_751] :
      ( k1_relat_1(A_751) = k1_xboole_0
      | ~ r1_tarski(A_751,k1_xboole_0)
      | ~ v1_relat_1(A_751) ) ),
    inference(resolution,[status(thm)],[c_9864,c_8])).

tff(c_13170,plain,
    ( k1_relat_1('#skF_9') = k1_xboole_0
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_13166,c_9874])).

tff(c_13184,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_10062,c_13170])).

tff(c_9859,plain,(
    ! [A_750] :
      ( v1_xboole_0(k1_relat_1(A_750))
      | ~ r1_tarski(A_750,k1_xboole_0)
      | ~ v1_relat_1(A_750) ) ),
    inference(resolution,[status(thm)],[c_9843,c_9587])).

tff(c_10075,plain,
    ( v1_xboole_0('#skF_7')
    | ~ r1_tarski('#skF_9',k1_xboole_0)
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_10062,c_9859])).

tff(c_10103,plain,
    ( v1_xboole_0('#skF_7')
    | ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_10075])).

tff(c_13167,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_10103])).

tff(c_13246,plain,(
    ~ r1_tarski('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13184,c_13167])).

tff(c_13192,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13184,c_13166])).

tff(c_13247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13246,c_13192])).

tff(c_13248,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_10103])).

tff(c_13315,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_13248,c_8])).

tff(c_13257,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_13248,c_8])).

tff(c_9653,plain,(
    ! [A_723] :
      ( r1_tarski(k1_relat_1(A_723),k1_xboole_0)
      | ~ r1_tarski(A_723,k1_xboole_0)
      | ~ v1_relat_1(A_723) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_9648])).

tff(c_10078,plain,
    ( r1_tarski('#skF_7',k1_xboole_0)
    | ~ r1_tarski('#skF_9',k1_xboole_0)
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_10062,c_9653])).

tff(c_10105,plain,
    ( r1_tarski('#skF_7',k1_xboole_0)
    | ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_10078])).

tff(c_13250,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_10105])).

tff(c_13295,plain,(
    ~ r1_tarski('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13257,c_13250])).

tff(c_13296,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13257,c_13166])).

tff(c_13297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13295,c_13296])).

tff(c_13299,plain,(
    r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_10105])).

tff(c_13355,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13315,c_13299])).

tff(c_13562,plain,(
    ! [A_969] :
      ( v1_xboole_0(A_969)
      | ~ r1_tarski(A_969,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13315,c_9587])).

tff(c_13570,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_13355,c_13562])).

tff(c_13341,plain,(
    ! [A_5] :
      ( A_5 = '#skF_7'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13315,c_8])).

tff(c_13576,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_13570,c_13341])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_13343,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_7',B_9) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13315,c_13315,c_20])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2430,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_2422,c_22])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2433,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') = '#skF_9'
    | ~ r1_tarski(k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_2430,c_10])).

tff(c_9530,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2433])).

tff(c_13488,plain,(
    ~ r1_tarski('#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13343,c_9530])).

tff(c_13610,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13576,c_13488])).

tff(c_13630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_13610])).

tff(c_13631,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2433])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_13641,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 != '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_13631,c_16])).

tff(c_13656,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_13641])).

tff(c_13962,plain,(
    ! [A_1005,B_1006,D_1007] :
      ( '#skF_5'(A_1005,B_1006,k1_funct_2(A_1005,B_1006),D_1007) = D_1007
      | ~ r2_hidden(D_1007,k1_funct_2(A_1005,B_1006)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_13969,plain,(
    '#skF_5'('#skF_7','#skF_8',k1_funct_2('#skF_7','#skF_8'),'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_106,c_13962])).

tff(c_14196,plain,(
    ! [A_1026,B_1027,D_1028] :
      ( k1_relat_1('#skF_5'(A_1026,B_1027,k1_funct_2(A_1026,B_1027),D_1028)) = A_1026
      | ~ r2_hidden(D_1028,k1_funct_2(A_1026,B_1027)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_14238,plain,
    ( k1_relat_1('#skF_9') = '#skF_7'
    | ~ r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13969,c_14196])).

tff(c_14242,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_14238])).

tff(c_13753,plain,(
    ! [A_988] :
      ( m1_subset_1(A_988,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_988),k2_relat_1(A_988))))
      | ~ v1_funct_1(A_988)
      | ~ v1_relat_1(A_988) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_13771,plain,(
    ! [A_988] :
      ( r1_tarski(A_988,k2_zfmisc_1(k1_relat_1(A_988),k2_relat_1(A_988)))
      | ~ v1_funct_1(A_988)
      | ~ v1_relat_1(A_988) ) ),
    inference(resolution,[status(thm)],[c_13753,c_22])).

tff(c_14249,plain,
    ( r1_tarski('#skF_9',k2_zfmisc_1('#skF_7',k2_relat_1('#skF_9')))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_14242,c_13771])).

tff(c_14282,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_7',k2_relat_1('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_611,c_14249])).

tff(c_13668,plain,(
    ! [C_974,B_975,A_976] :
      ( v1_xboole_0(C_974)
      | ~ m1_subset_1(C_974,k1_zfmisc_1(k2_zfmisc_1(B_975,A_976)))
      | ~ v1_xboole_0(A_976) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_13682,plain,(
    ! [A_10,A_976,B_975] :
      ( v1_xboole_0(A_10)
      | ~ v1_xboole_0(A_976)
      | ~ r1_tarski(A_10,k2_zfmisc_1(B_975,A_976)) ) ),
    inference(resolution,[status(thm)],[c_24,c_13668])).

tff(c_14337,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_14282,c_13682])).

tff(c_14344,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_14337])).

tff(c_13634,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13631,c_2422])).

tff(c_14387,plain,(
    ! [C_1034,A_1035,B_1036] :
      ( v1_funct_2(C_1034,A_1035,B_1036)
      | ~ v1_partfun1(C_1034,A_1035)
      | ~ v1_funct_1(C_1034)
      | ~ m1_subset_1(C_1034,k1_zfmisc_1(k2_zfmisc_1(A_1035,B_1036))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_14862,plain,(
    ! [C_1059] :
      ( v1_funct_2(C_1059,'#skF_7','#skF_8')
      | ~ v1_partfun1(C_1059,'#skF_7')
      | ~ v1_funct_1(C_1059)
      | ~ m1_subset_1(C_1059,k1_zfmisc_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13631,c_14387])).

tff(c_14865,plain,
    ( v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_partfun1('#skF_9','#skF_7')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_13634,c_14862])).

tff(c_14872,plain,
    ( v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_partfun1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_14865])).

tff(c_14873,plain,(
    ~ v1_partfun1('#skF_9','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_2421,c_14872])).

tff(c_14276,plain,
    ( v1_funct_2('#skF_9','#skF_7',k2_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_14242,c_88])).

tff(c_14300,plain,(
    v1_funct_2('#skF_9','#skF_7',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_611,c_14276])).

tff(c_14273,plain,
    ( m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k2_relat_1('#skF_9'))))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_14242,c_86])).

tff(c_14298,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k2_relat_1('#skF_9')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_611,c_14273])).

tff(c_15773,plain,(
    ! [C_1121,A_1122,B_1123] :
      ( v1_partfun1(C_1121,A_1122)
      | ~ v1_funct_2(C_1121,A_1122,B_1123)
      | ~ v1_funct_1(C_1121)
      | ~ m1_subset_1(C_1121,k1_zfmisc_1(k2_zfmisc_1(A_1122,B_1123)))
      | v1_xboole_0(B_1123) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_15779,plain,
    ( v1_partfun1('#skF_9','#skF_7')
    | ~ v1_funct_2('#skF_9','#skF_7',k2_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_14298,c_15773])).

tff(c_15808,plain,
    ( v1_partfun1('#skF_9','#skF_7')
    | v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_14300,c_15779])).

tff(c_15810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14344,c_14873,c_15808])).

tff(c_15811,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_14337])).

tff(c_15817,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_15811,c_8])).

tff(c_15822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13656,c_15817])).

tff(c_15824,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_13641])).

tff(c_15836,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15824,c_6])).

tff(c_15835,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15824,c_15824,c_34])).

tff(c_18143,plain,(
    ! [C_1322,B_1323] :
      ( r2_hidden('#skF_6'(k1_relat_1(C_1322),B_1323,C_1322),k1_relat_1(C_1322))
      | v1_funct_2(C_1322,k1_relat_1(C_1322),B_1323)
      | ~ v1_funct_1(C_1322)
      | ~ v1_relat_1(C_1322) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_18173,plain,(
    ! [B_1323] :
      ( r2_hidden('#skF_6'('#skF_9',B_1323,'#skF_9'),k1_relat_1('#skF_9'))
      | v1_funct_2('#skF_9',k1_relat_1('#skF_9'),B_1323)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15835,c_18143])).

tff(c_18182,plain,(
    ! [B_1324] :
      ( r2_hidden('#skF_6'('#skF_9',B_1324,'#skF_9'),'#skF_9')
      | v1_funct_2('#skF_9','#skF_9',B_1324) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_611,c_15835,c_15835,c_18173])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18185,plain,(
    ! [B_1324] :
      ( ~ v1_xboole_0('#skF_9')
      | v1_funct_2('#skF_9','#skF_9',B_1324) ) ),
    inference(resolution,[status(thm)],[c_18182,c_2])).

tff(c_18188,plain,(
    ! [B_1324] : v1_funct_2('#skF_9','#skF_9',B_1324) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15836,c_18185])).

tff(c_15823,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_13641])).

tff(c_15927,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15824,c_15824,c_15823])).

tff(c_15928,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_15927])).

tff(c_2749,plain,(
    ! [A_299,B_300,D_301] :
      ( '#skF_5'(A_299,B_300,k1_funct_2(A_299,B_300),D_301) = D_301
      | ~ r2_hidden(D_301,k1_funct_2(A_299,B_300)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2756,plain,(
    '#skF_5'('#skF_7','#skF_8',k1_funct_2('#skF_7','#skF_8'),'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_106,c_2749])).

tff(c_2964,plain,(
    ! [A_317,B_318,D_319] :
      ( k1_relat_1('#skF_5'(A_317,B_318,k1_funct_2(A_317,B_318),D_319)) = A_317
      | ~ r2_hidden(D_319,k1_funct_2(A_317,B_318)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3009,plain,
    ( k1_relat_1('#skF_9') = '#skF_7'
    | ~ r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2756,c_2964])).

tff(c_3013,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3009])).

tff(c_2509,plain,(
    ! [A_274] :
      ( m1_subset_1(A_274,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_274),k2_relat_1(A_274))))
      | ~ v1_funct_1(A_274)
      | ~ v1_relat_1(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2527,plain,(
    ! [A_274] :
      ( r1_tarski(A_274,k2_zfmisc_1(k1_relat_1(A_274),k2_relat_1(A_274)))
      | ~ v1_funct_1(A_274)
      | ~ v1_relat_1(A_274) ) ),
    inference(resolution,[status(thm)],[c_2509,c_22])).

tff(c_3023,plain,
    ( r1_tarski('#skF_9',k2_zfmisc_1('#skF_7',k2_relat_1('#skF_9')))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3013,c_2527])).

tff(c_3058,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_7',k2_relat_1('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_611,c_3023])).

tff(c_2463,plain,(
    ! [C_267,B_268,A_269] :
      ( v1_xboole_0(C_267)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(B_268,A_269)))
      | ~ v1_xboole_0(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2478,plain,(
    ! [A_10,A_269,B_268] :
      ( v1_xboole_0(A_10)
      | ~ v1_xboole_0(A_269)
      | ~ r1_tarski(A_10,k2_zfmisc_1(B_268,A_269)) ) ),
    inference(resolution,[status(thm)],[c_24,c_2463])).

tff(c_5351,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_3058,c_2478])).

tff(c_5362,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_5351])).

tff(c_5606,plain,(
    ! [C_467,A_468,B_469] :
      ( v1_funct_2(C_467,A_468,B_469)
      | ~ v1_partfun1(C_467,A_468)
      | ~ v1_funct_1(C_467)
      | ~ m1_subset_1(C_467,k1_zfmisc_1(k2_zfmisc_1(A_468,B_469))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5624,plain,
    ( v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_partfun1('#skF_9','#skF_7')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_2422,c_5606])).

tff(c_5641,plain,
    ( v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_partfun1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_5624])).

tff(c_5642,plain,(
    ~ v1_partfun1('#skF_9','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_2421,c_5641])).

tff(c_3050,plain,
    ( v1_funct_2('#skF_9','#skF_7',k2_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3013,c_88])).

tff(c_3076,plain,(
    v1_funct_2('#skF_9','#skF_7',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_611,c_3050])).

tff(c_3047,plain,
    ( m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k2_relat_1('#skF_9'))))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3013,c_86])).

tff(c_3074,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k2_relat_1('#skF_9')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_611,c_3047])).

tff(c_6573,plain,(
    ! [C_529,A_530,B_531] :
      ( v1_partfun1(C_529,A_530)
      | ~ v1_funct_2(C_529,A_530,B_531)
      | ~ v1_funct_1(C_529)
      | ~ m1_subset_1(C_529,k1_zfmisc_1(k2_zfmisc_1(A_530,B_531)))
      | v1_xboole_0(B_531) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6579,plain,
    ( v1_partfun1('#skF_9','#skF_7')
    | ~ v1_funct_2('#skF_9','#skF_7',k2_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_3074,c_6573])).

tff(c_6608,plain,
    ( v1_partfun1('#skF_9','#skF_7')
    | v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_3076,c_6579])).

tff(c_6610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5362,c_5642,c_6608])).

tff(c_6611,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_5351])).

tff(c_6619,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6611,c_8])).

tff(c_2636,plain,(
    ! [A_286,B_287] :
      ( r1_tarski(k1_relat_1(A_286),k1_relat_1(B_287))
      | ~ r1_tarski(A_286,B_287)
      | ~ v1_relat_1(B_287)
      | ~ v1_relat_1(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2644,plain,(
    ! [A_286] :
      ( r1_tarski(k1_relat_1(A_286),k1_xboole_0)
      | ~ r1_tarski(A_286,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_286) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2636])).

tff(c_2709,plain,(
    ! [A_296] :
      ( r1_tarski(k1_relat_1(A_296),k1_xboole_0)
      | ~ r1_tarski(A_296,k1_xboole_0)
      | ~ v1_relat_1(A_296) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_2644])).

tff(c_2726,plain,(
    ! [A_296] :
      ( v1_relat_1(k1_relat_1(A_296))
      | ~ r1_tarski(A_296,k1_xboole_0)
      | ~ v1_relat_1(A_296) ) ),
    inference(resolution,[status(thm)],[c_2709,c_200])).

tff(c_3032,plain,
    ( v1_relat_1('#skF_7')
    | ~ r1_tarski('#skF_9',k1_xboole_0)
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3013,c_2726])).

tff(c_3064,plain,
    ( v1_relat_1('#skF_7')
    | ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_3032])).

tff(c_3078,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3064])).

tff(c_6623,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6619,c_3078])).

tff(c_6657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6623])).

tff(c_6659,plain,(
    r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3064])).

tff(c_2473,plain,(
    ! [C_267] :
      ( v1_xboole_0(C_267)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2463])).

tff(c_2496,plain,(
    ! [C_272] :
      ( v1_xboole_0(C_272)
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2473])).

tff(c_2501,plain,(
    ! [A_10] :
      ( v1_xboole_0(A_10)
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_2496])).

tff(c_2730,plain,(
    ! [A_297] :
      ( v1_xboole_0(k1_relat_1(A_297))
      | ~ r1_tarski(A_297,k1_xboole_0)
      | ~ v1_relat_1(A_297) ) ),
    inference(resolution,[status(thm)],[c_2709,c_2501])).

tff(c_2740,plain,(
    ! [A_297] :
      ( k1_relat_1(A_297) = k1_xboole_0
      | ~ r1_tarski(A_297,k1_xboole_0)
      | ~ v1_relat_1(A_297) ) ),
    inference(resolution,[status(thm)],[c_2730,c_8])).

tff(c_6663,plain,
    ( k1_relat_1('#skF_9') = k1_xboole_0
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_6659,c_2740])).

tff(c_6677,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_3013,c_6663])).

tff(c_2725,plain,(
    ! [A_296] :
      ( v1_xboole_0(k1_relat_1(A_296))
      | ~ r1_tarski(A_296,k1_xboole_0)
      | ~ v1_relat_1(A_296) ) ),
    inference(resolution,[status(thm)],[c_2709,c_2501])).

tff(c_3035,plain,
    ( v1_xboole_0('#skF_7')
    | ~ r1_tarski('#skF_9',k1_xboole_0)
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3013,c_2725])).

tff(c_3066,plain,
    ( v1_xboole_0('#skF_7')
    | ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_3035])).

tff(c_6660,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3066])).

tff(c_6738,plain,(
    ~ r1_tarski('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6677,c_6660])).

tff(c_6685,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6677,c_6659])).

tff(c_6790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6738,c_6685])).

tff(c_6791,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_3066])).

tff(c_6799,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6791,c_8])).

tff(c_6836,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6799,c_6659])).

tff(c_7051,plain,(
    ! [A_545] :
      ( v1_xboole_0(A_545)
      | ~ r1_tarski(A_545,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6799,c_2501])).

tff(c_7059,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_6836,c_7051])).

tff(c_6824,plain,(
    ! [A_5] :
      ( A_5 = '#skF_7'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6799,c_8])).

tff(c_7065,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_7059,c_6824])).

tff(c_6826,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_7',B_9) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6799,c_6799,c_20])).

tff(c_2446,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2433])).

tff(c_6982,plain,(
    ~ r1_tarski('#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6826,c_2446])).

tff(c_7069,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7065,c_6982])).

tff(c_7089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_7069])).

tff(c_7090,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2433])).

tff(c_7122,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 != '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_7090,c_16])).

tff(c_7148,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_7122])).

tff(c_7433,plain,(
    ! [A_582,B_583,D_584] :
      ( '#skF_5'(A_582,B_583,k1_funct_2(A_582,B_583),D_584) = D_584
      | ~ r2_hidden(D_584,k1_funct_2(A_582,B_583)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_7440,plain,(
    '#skF_5'('#skF_7','#skF_8',k1_funct_2('#skF_7','#skF_8'),'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_106,c_7433])).

tff(c_7621,plain,(
    ! [A_597,B_598,D_599] :
      ( k1_relat_1('#skF_5'(A_597,B_598,k1_funct_2(A_597,B_598),D_599)) = A_597
      | ~ r2_hidden(D_599,k1_funct_2(A_597,B_598)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_7663,plain,
    ( k1_relat_1('#skF_9') = '#skF_7'
    | ~ r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7440,c_7621])).

tff(c_7667,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_7663])).

tff(c_7149,plain,(
    ! [A_551] :
      ( m1_subset_1(A_551,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_551),k2_relat_1(A_551))))
      | ~ v1_funct_1(A_551)
      | ~ v1_relat_1(A_551) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_7167,plain,(
    ! [A_551] :
      ( r1_tarski(A_551,k2_zfmisc_1(k1_relat_1(A_551),k2_relat_1(A_551)))
      | ~ v1_funct_1(A_551)
      | ~ v1_relat_1(A_551) ) ),
    inference(resolution,[status(thm)],[c_7149,c_22])).

tff(c_7674,plain,
    ( r1_tarski('#skF_9',k2_zfmisc_1('#skF_7',k2_relat_1('#skF_9')))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_7667,c_7167])).

tff(c_7707,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_7',k2_relat_1('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_611,c_7674])).

tff(c_7092,plain,(
    ! [C_546,B_547,A_548] :
      ( v1_xboole_0(C_546)
      | ~ m1_subset_1(C_546,k1_zfmisc_1(k2_zfmisc_1(B_547,A_548)))
      | ~ v1_xboole_0(A_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_7107,plain,(
    ! [A_10,A_548,B_547] :
      ( v1_xboole_0(A_10)
      | ~ v1_xboole_0(A_548)
      | ~ r1_tarski(A_10,k2_zfmisc_1(B_547,A_548)) ) ),
    inference(resolution,[status(thm)],[c_24,c_7092])).

tff(c_7762,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_7707,c_7107])).

tff(c_7769,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_7762])).

tff(c_7112,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7090,c_2422])).

tff(c_7926,plain,(
    ! [C_610,A_611,B_612] :
      ( v1_funct_2(C_610,A_611,B_612)
      | ~ v1_partfun1(C_610,A_611)
      | ~ v1_funct_1(C_610)
      | ~ m1_subset_1(C_610,k1_zfmisc_1(k2_zfmisc_1(A_611,B_612))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8283,plain,(
    ! [C_628] :
      ( v1_funct_2(C_628,'#skF_7','#skF_8')
      | ~ v1_partfun1(C_628,'#skF_7')
      | ~ v1_funct_1(C_628)
      | ~ m1_subset_1(C_628,k1_zfmisc_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7090,c_7926])).

tff(c_8286,plain,
    ( v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_partfun1('#skF_9','#skF_7')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_7112,c_8283])).

tff(c_8293,plain,
    ( v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_partfun1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_8286])).

tff(c_8294,plain,(
    ~ v1_partfun1('#skF_9','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_2421,c_8293])).

tff(c_7701,plain,
    ( v1_funct_2('#skF_9','#skF_7',k2_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_7667,c_88])).

tff(c_7725,plain,(
    v1_funct_2('#skF_9','#skF_7',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_611,c_7701])).

tff(c_7698,plain,
    ( m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k2_relat_1('#skF_9'))))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_7667,c_86])).

tff(c_7723,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k2_relat_1('#skF_9')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_611,c_7698])).

tff(c_9460,plain,(
    ! [C_708,A_709,B_710] :
      ( v1_partfun1(C_708,A_709)
      | ~ v1_funct_2(C_708,A_709,B_710)
      | ~ v1_funct_1(C_708)
      | ~ m1_subset_1(C_708,k1_zfmisc_1(k2_zfmisc_1(A_709,B_710)))
      | v1_xboole_0(B_710) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_9466,plain,
    ( v1_partfun1('#skF_9','#skF_7')
    | ~ v1_funct_2('#skF_9','#skF_7',k2_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_7723,c_9460])).

tff(c_9495,plain,
    ( v1_partfun1('#skF_9','#skF_7')
    | v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_7725,c_9466])).

tff(c_9497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7769,c_8294,c_9495])).

tff(c_9498,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_7762])).

tff(c_9504,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_9498,c_8])).

tff(c_9509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7148,c_9504])).

tff(c_9511,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_7122])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2434,plain,(
    ! [A_263] :
      ( v1_funct_2(A_263,k1_relat_1(A_263),k2_relat_1(A_263))
      | ~ v1_funct_1(A_263)
      | ~ v1_relat_1(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2437,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2434])).

tff(c_2442,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_34,c_2437])).

tff(c_2445,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2442])).

tff(c_9514,plain,(
    ~ v1_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9511,c_2445])).

tff(c_9527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_9514])).

tff(c_9528,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2442])).

tff(c_15825,plain,(
    v1_funct_2('#skF_9','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15824,c_15824,c_15824,c_9528])).

tff(c_15932,plain,(
    v1_funct_2('#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15928,c_15928,c_15928,c_15825])).

tff(c_15943,plain,(
    r2_hidden('#skF_8',k1_funct_2('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15928,c_106])).

tff(c_15933,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15928,c_15928,c_15835])).

tff(c_16124,plain,(
    ! [A_1143,B_1144,D_1145] :
      ( '#skF_5'(A_1143,B_1144,k1_funct_2(A_1143,B_1144),D_1145) = D_1145
      | ~ r2_hidden(D_1145,k1_funct_2(A_1143,B_1144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_16130,plain,(
    '#skF_5'('#skF_7','#skF_8',k1_funct_2('#skF_7','#skF_8'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_15943,c_16124])).

tff(c_16379,plain,(
    ! [A_1179,B_1180,D_1181] :
      ( k1_relat_1('#skF_5'(A_1179,B_1180,k1_funct_2(A_1179,B_1180),D_1181)) = A_1179
      | ~ r2_hidden(D_1181,k1_funct_2(A_1179,B_1180)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_16415,plain,
    ( k1_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16130,c_16379])).

tff(c_16419,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15943,c_15933,c_16415])).

tff(c_15941,plain,(
    ~ v1_funct_2('#skF_8','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15928,c_2421])).

tff(c_16421,plain,(
    ~ v1_funct_2('#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16419,c_15941])).

tff(c_16426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15932,c_16421])).

tff(c_16427,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_15927])).

tff(c_16430,plain,(
    ~ v1_funct_2('#skF_9','#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16427,c_2421])).

tff(c_18193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18188,c_16430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:47:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.89/3.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.89/3.60  
% 9.89/3.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.89/3.61  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 9.89/3.61  
% 9.89/3.61  %Foreground sorts:
% 9.89/3.61  
% 9.89/3.61  
% 9.89/3.61  %Background operators:
% 9.89/3.61  
% 9.89/3.61  
% 9.89/3.61  %Foreground operators:
% 9.89/3.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.89/3.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.89/3.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.89/3.61  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.89/3.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.89/3.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.89/3.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.89/3.61  tff('#skF_7', type, '#skF_7': $i).
% 9.89/3.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.89/3.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.89/3.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.89/3.61  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.89/3.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.89/3.61  tff('#skF_9', type, '#skF_9': $i).
% 9.89/3.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.89/3.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.89/3.61  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 9.89/3.61  tff('#skF_8', type, '#skF_8': $i).
% 9.89/3.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.89/3.61  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 9.89/3.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.89/3.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.89/3.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.89/3.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.89/3.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.89/3.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.89/3.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.89/3.61  
% 10.15/3.64  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.15/3.64  tff(f_163, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 10.15/3.64  tff(f_127, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 10.15/3.64  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 10.15/3.64  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.15/3.64  tff(f_137, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 10.15/3.64  tff(f_79, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 10.15/3.64  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 10.15/3.64  tff(f_111, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 10.15/3.64  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.15/3.64  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.15/3.64  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.15/3.64  tff(f_68, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 10.15/3.64  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 10.15/3.64  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.15/3.64  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.15/3.64  tff(f_154, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 10.15/3.64  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.15/3.64  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.15/3.64  tff(c_106, plain, (r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 10.15/3.64  tff(c_888, plain, (![A_159, B_160, D_161]: ('#skF_5'(A_159, B_160, k1_funct_2(A_159, B_160), D_161)=D_161 | ~r2_hidden(D_161, k1_funct_2(A_159, B_160)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_895, plain, ('#skF_5'('#skF_7', '#skF_8', k1_funct_2('#skF_7', '#skF_8'), '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_106, c_888])).
% 10.15/3.64  tff(c_938, plain, (![A_164, B_165, D_166]: (v1_relat_1('#skF_5'(A_164, B_165, k1_funct_2(A_164, B_165), D_166)) | ~r2_hidden(D_166, k1_funct_2(A_164, B_165)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_941, plain, (v1_relat_1('#skF_9') | ~r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_895, c_938])).
% 10.15/3.64  tff(c_943, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_941])).
% 10.15/3.64  tff(c_1106, plain, (![A_178, B_179, D_180]: (k1_relat_1('#skF_5'(A_178, B_179, k1_funct_2(A_178, B_179), D_180))=A_178 | ~r2_hidden(D_180, k1_funct_2(A_178, B_179)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_1145, plain, (k1_relat_1('#skF_9')='#skF_7' | ~r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_895, c_1106])).
% 10.15/3.64  tff(c_1149, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1145])).
% 10.15/3.64  tff(c_1360, plain, (![A_194, B_195, D_196]: (r1_tarski(k2_relat_1('#skF_5'(A_194, B_195, k1_funct_2(A_194, B_195), D_196)), B_195) | ~r2_hidden(D_196, k1_funct_2(A_194, B_195)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_1393, plain, (r1_tarski(k2_relat_1('#skF_9'), '#skF_8') | ~r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_895, c_1360])).
% 10.15/3.64  tff(c_1403, plain, (r1_tarski(k2_relat_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1393])).
% 10.15/3.64  tff(c_2384, plain, (![C_260, A_261, B_262]: (m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~r1_tarski(k2_relat_1(C_260), B_262) | ~r1_tarski(k1_relat_1(C_260), A_261) | ~v1_relat_1(C_260))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.15/3.64  tff(c_104, plain, (~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_163])).
% 10.15/3.64  tff(c_201, plain, (~v1_funct_1('#skF_9')), inference(splitLeft, [status(thm)], [c_104])).
% 10.15/3.64  tff(c_512, plain, (![A_117, B_118, D_119]: ('#skF_5'(A_117, B_118, k1_funct_2(A_117, B_118), D_119)=D_119 | ~r2_hidden(D_119, k1_funct_2(A_117, B_118)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_519, plain, ('#skF_5'('#skF_7', '#skF_8', k1_funct_2('#skF_7', '#skF_8'), '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_106, c_512])).
% 10.15/3.64  tff(c_602, plain, (![A_124, B_125, D_126]: (v1_funct_1('#skF_5'(A_124, B_125, k1_funct_2(A_124, B_125), D_126)) | ~r2_hidden(D_126, k1_funct_2(A_124, B_125)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_605, plain, (v1_funct_1('#skF_9') | ~r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_519, c_602])).
% 10.15/3.64  tff(c_607, plain, (v1_funct_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_605])).
% 10.15/3.64  tff(c_609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_607])).
% 10.15/3.64  tff(c_610, plain, (~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(splitRight, [status(thm)], [c_104])).
% 10.15/3.64  tff(c_619, plain, (~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(splitLeft, [status(thm)], [c_610])).
% 10.15/3.64  tff(c_2393, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_8') | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_7') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_2384, c_619])).
% 10.15/3.64  tff(c_2420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_943, c_14, c_1149, c_1403, c_2393])).
% 10.15/3.64  tff(c_2422, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(splitRight, [status(thm)], [c_610])).
% 10.15/3.64  tff(c_36, plain, (![C_19, A_17, B_18]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.15/3.64  tff(c_2429, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_2422, c_36])).
% 10.15/3.64  tff(c_9799, plain, (![A_742, B_743, D_744]: ('#skF_5'(A_742, B_743, k1_funct_2(A_742, B_743), D_744)=D_744 | ~r2_hidden(D_744, k1_funct_2(A_742, B_743)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_9806, plain, ('#skF_5'('#skF_7', '#skF_8', k1_funct_2('#skF_7', '#skF_8'), '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_106, c_9799])).
% 10.15/3.64  tff(c_10019, plain, (![A_762, B_763, D_764]: (k1_relat_1('#skF_5'(A_762, B_763, k1_funct_2(A_762, B_763), D_764))=A_762 | ~r2_hidden(D_764, k1_funct_2(A_762, B_763)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_10058, plain, (k1_relat_1('#skF_9')='#skF_7' | ~r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_9806, c_10019])).
% 10.15/3.64  tff(c_10062, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_10058])).
% 10.15/3.64  tff(c_611, plain, (v1_funct_1('#skF_9')), inference(splitRight, [status(thm)], [c_104])).
% 10.15/3.64  tff(c_86, plain, (![A_54]: (m1_subset_1(A_54, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_54), k2_relat_1(A_54)))) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_137])).
% 10.15/3.64  tff(c_10090, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k2_relat_1('#skF_9')))) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_10062, c_86])).
% 10.15/3.64  tff(c_10113, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k2_relat_1('#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_611, c_10090])).
% 10.15/3.64  tff(c_38, plain, (![C_23, B_21, A_20]: (v1_xboole_0(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(B_21, A_20))) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.15/3.64  tff(c_11476, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0(k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_10113, c_38])).
% 10.15/3.64  tff(c_11482, plain, (~v1_xboole_0(k2_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_11476])).
% 10.15/3.64  tff(c_2421, plain, (~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_610])).
% 10.15/3.64  tff(c_11585, plain, (![C_853, A_854, B_855]: (v1_funct_2(C_853, A_854, B_855) | ~v1_partfun1(C_853, A_854) | ~v1_funct_1(C_853) | ~m1_subset_1(C_853, k1_zfmisc_1(k2_zfmisc_1(A_854, B_855))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.15/3.64  tff(c_11603, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_partfun1('#skF_9', '#skF_7') | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_2422, c_11585])).
% 10.15/3.64  tff(c_11620, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_partfun1('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_611, c_11603])).
% 10.15/3.64  tff(c_11621, plain, (~v1_partfun1('#skF_9', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_2421, c_11620])).
% 10.15/3.64  tff(c_88, plain, (![A_54]: (v1_funct_2(A_54, k1_relat_1(A_54), k2_relat_1(A_54)) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_137])).
% 10.15/3.64  tff(c_10093, plain, (v1_funct_2('#skF_9', '#skF_7', k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_10062, c_88])).
% 10.15/3.64  tff(c_10115, plain, (v1_funct_2('#skF_9', '#skF_7', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_611, c_10093])).
% 10.15/3.64  tff(c_13079, plain, (![C_950, A_951, B_952]: (v1_partfun1(C_950, A_951) | ~v1_funct_2(C_950, A_951, B_952) | ~v1_funct_1(C_950) | ~m1_subset_1(C_950, k1_zfmisc_1(k2_zfmisc_1(A_951, B_952))) | v1_xboole_0(B_952))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.15/3.64  tff(c_13085, plain, (v1_partfun1('#skF_9', '#skF_7') | ~v1_funct_2('#skF_9', '#skF_7', k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | v1_xboole_0(k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_10113, c_13079])).
% 10.15/3.64  tff(c_13114, plain, (v1_partfun1('#skF_9', '#skF_7') | v1_xboole_0(k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_611, c_10115, c_13085])).
% 10.15/3.64  tff(c_13116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11482, c_11621, c_13114])).
% 10.15/3.64  tff(c_13117, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_11476])).
% 10.15/3.64  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.15/3.64  tff(c_13125, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_13117, c_8])).
% 10.15/3.64  tff(c_118, plain, (![B_62]: (k2_zfmisc_1(k1_xboole_0, B_62)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.15/3.64  tff(c_26, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.15/3.64  tff(c_122, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_118, c_26])).
% 10.15/3.64  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.15/3.64  tff(c_9640, plain, (![A_723, B_724]: (r1_tarski(k1_relat_1(A_723), k1_relat_1(B_724)) | ~r1_tarski(A_723, B_724) | ~v1_relat_1(B_724) | ~v1_relat_1(A_723))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.15/3.64  tff(c_9648, plain, (![A_723]: (r1_tarski(k1_relat_1(A_723), k1_xboole_0) | ~r1_tarski(A_723, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_723))), inference(superposition, [status(thm), theory('equality')], [c_34, c_9640])).
% 10.15/3.64  tff(c_9843, plain, (![A_750]: (r1_tarski(k1_relat_1(A_750), k1_xboole_0) | ~r1_tarski(A_750, k1_xboole_0) | ~v1_relat_1(A_750))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_9648])).
% 10.15/3.64  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.15/3.64  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.15/3.64  tff(c_185, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.15/3.64  tff(c_195, plain, (![C_79]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_185])).
% 10.15/3.64  tff(c_200, plain, (![A_10]: (v1_relat_1(A_10) | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_195])).
% 10.15/3.64  tff(c_9860, plain, (![A_750]: (v1_relat_1(k1_relat_1(A_750)) | ~r1_tarski(A_750, k1_xboole_0) | ~v1_relat_1(A_750))), inference(resolution, [status(thm)], [c_9843, c_200])).
% 10.15/3.64  tff(c_10072, plain, (v1_relat_1('#skF_7') | ~r1_tarski('#skF_9', k1_xboole_0) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_10062, c_9860])).
% 10.15/3.64  tff(c_10101, plain, (v1_relat_1('#skF_7') | ~r1_tarski('#skF_9', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_10072])).
% 10.15/3.64  tff(c_10117, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_10101])).
% 10.15/3.64  tff(c_13129, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_13125, c_10117])).
% 10.15/3.64  tff(c_13164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_13129])).
% 10.15/3.64  tff(c_13166, plain, (r1_tarski('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_10101])).
% 10.15/3.64  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.15/3.64  tff(c_9549, plain, (![C_714, B_715, A_716]: (v1_xboole_0(C_714) | ~m1_subset_1(C_714, k1_zfmisc_1(k2_zfmisc_1(B_715, A_716))) | ~v1_xboole_0(A_716))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.15/3.64  tff(c_9559, plain, (![C_714]: (v1_xboole_0(C_714) | ~m1_subset_1(C_714, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_9549])).
% 10.15/3.64  tff(c_9582, plain, (![C_719]: (v1_xboole_0(C_719) | ~m1_subset_1(C_719, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_9559])).
% 10.15/3.64  tff(c_9587, plain, (![A_10]: (v1_xboole_0(A_10) | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_9582])).
% 10.15/3.64  tff(c_9864, plain, (![A_751]: (v1_xboole_0(k1_relat_1(A_751)) | ~r1_tarski(A_751, k1_xboole_0) | ~v1_relat_1(A_751))), inference(resolution, [status(thm)], [c_9843, c_9587])).
% 10.15/3.64  tff(c_9874, plain, (![A_751]: (k1_relat_1(A_751)=k1_xboole_0 | ~r1_tarski(A_751, k1_xboole_0) | ~v1_relat_1(A_751))), inference(resolution, [status(thm)], [c_9864, c_8])).
% 10.15/3.64  tff(c_13170, plain, (k1_relat_1('#skF_9')=k1_xboole_0 | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_13166, c_9874])).
% 10.15/3.64  tff(c_13184, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_10062, c_13170])).
% 10.15/3.64  tff(c_9859, plain, (![A_750]: (v1_xboole_0(k1_relat_1(A_750)) | ~r1_tarski(A_750, k1_xboole_0) | ~v1_relat_1(A_750))), inference(resolution, [status(thm)], [c_9843, c_9587])).
% 10.15/3.64  tff(c_10075, plain, (v1_xboole_0('#skF_7') | ~r1_tarski('#skF_9', k1_xboole_0) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_10062, c_9859])).
% 10.15/3.64  tff(c_10103, plain, (v1_xboole_0('#skF_7') | ~r1_tarski('#skF_9', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_10075])).
% 10.15/3.64  tff(c_13167, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_10103])).
% 10.15/3.64  tff(c_13246, plain, (~r1_tarski('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13184, c_13167])).
% 10.15/3.64  tff(c_13192, plain, (r1_tarski('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13184, c_13166])).
% 10.15/3.64  tff(c_13247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13246, c_13192])).
% 10.15/3.64  tff(c_13248, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_10103])).
% 10.15/3.64  tff(c_13315, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_13248, c_8])).
% 10.15/3.64  tff(c_13257, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_13248, c_8])).
% 10.15/3.64  tff(c_9653, plain, (![A_723]: (r1_tarski(k1_relat_1(A_723), k1_xboole_0) | ~r1_tarski(A_723, k1_xboole_0) | ~v1_relat_1(A_723))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_9648])).
% 10.15/3.64  tff(c_10078, plain, (r1_tarski('#skF_7', k1_xboole_0) | ~r1_tarski('#skF_9', k1_xboole_0) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_10062, c_9653])).
% 10.15/3.64  tff(c_10105, plain, (r1_tarski('#skF_7', k1_xboole_0) | ~r1_tarski('#skF_9', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_10078])).
% 10.15/3.64  tff(c_13250, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_10105])).
% 10.15/3.64  tff(c_13295, plain, (~r1_tarski('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13257, c_13250])).
% 10.15/3.64  tff(c_13296, plain, (r1_tarski('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13257, c_13166])).
% 10.15/3.64  tff(c_13297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13295, c_13296])).
% 10.15/3.64  tff(c_13299, plain, (r1_tarski('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_10105])).
% 10.15/3.64  tff(c_13355, plain, (r1_tarski('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13315, c_13299])).
% 10.15/3.64  tff(c_13562, plain, (![A_969]: (v1_xboole_0(A_969) | ~r1_tarski(A_969, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_13315, c_9587])).
% 10.15/3.64  tff(c_13570, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_13355, c_13562])).
% 10.15/3.64  tff(c_13341, plain, (![A_5]: (A_5='#skF_7' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_13315, c_8])).
% 10.15/3.64  tff(c_13576, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_13570, c_13341])).
% 10.15/3.64  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.15/3.64  tff(c_13343, plain, (![B_9]: (k2_zfmisc_1('#skF_7', B_9)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13315, c_13315, c_20])).
% 10.15/3.64  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.15/3.64  tff(c_2430, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_2422, c_22])).
% 10.15/3.64  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.15/3.64  tff(c_2433, plain, (k2_zfmisc_1('#skF_7', '#skF_8')='#skF_9' | ~r1_tarski(k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_2430, c_10])).
% 10.15/3.64  tff(c_9530, plain, (~r1_tarski(k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_2433])).
% 10.15/3.64  tff(c_13488, plain, (~r1_tarski('#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_13343, c_9530])).
% 10.15/3.64  tff(c_13610, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_13576, c_13488])).
% 10.15/3.64  tff(c_13630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_13610])).
% 10.15/3.64  tff(c_13631, plain, (k2_zfmisc_1('#skF_7', '#skF_8')='#skF_9'), inference(splitRight, [status(thm)], [c_2433])).
% 10.15/3.64  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.15/3.64  tff(c_13641, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0!='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_13631, c_16])).
% 10.15/3.64  tff(c_13656, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_13641])).
% 10.15/3.64  tff(c_13962, plain, (![A_1005, B_1006, D_1007]: ('#skF_5'(A_1005, B_1006, k1_funct_2(A_1005, B_1006), D_1007)=D_1007 | ~r2_hidden(D_1007, k1_funct_2(A_1005, B_1006)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_13969, plain, ('#skF_5'('#skF_7', '#skF_8', k1_funct_2('#skF_7', '#skF_8'), '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_106, c_13962])).
% 10.15/3.64  tff(c_14196, plain, (![A_1026, B_1027, D_1028]: (k1_relat_1('#skF_5'(A_1026, B_1027, k1_funct_2(A_1026, B_1027), D_1028))=A_1026 | ~r2_hidden(D_1028, k1_funct_2(A_1026, B_1027)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_14238, plain, (k1_relat_1('#skF_9')='#skF_7' | ~r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_13969, c_14196])).
% 10.15/3.64  tff(c_14242, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_14238])).
% 10.15/3.64  tff(c_13753, plain, (![A_988]: (m1_subset_1(A_988, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_988), k2_relat_1(A_988)))) | ~v1_funct_1(A_988) | ~v1_relat_1(A_988))), inference(cnfTransformation, [status(thm)], [f_137])).
% 10.15/3.64  tff(c_13771, plain, (![A_988]: (r1_tarski(A_988, k2_zfmisc_1(k1_relat_1(A_988), k2_relat_1(A_988))) | ~v1_funct_1(A_988) | ~v1_relat_1(A_988))), inference(resolution, [status(thm)], [c_13753, c_22])).
% 10.15/3.64  tff(c_14249, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_7', k2_relat_1('#skF_9'))) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_14242, c_13771])).
% 10.15/3.64  tff(c_14282, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_7', k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_611, c_14249])).
% 10.15/3.64  tff(c_13668, plain, (![C_974, B_975, A_976]: (v1_xboole_0(C_974) | ~m1_subset_1(C_974, k1_zfmisc_1(k2_zfmisc_1(B_975, A_976))) | ~v1_xboole_0(A_976))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.15/3.64  tff(c_13682, plain, (![A_10, A_976, B_975]: (v1_xboole_0(A_10) | ~v1_xboole_0(A_976) | ~r1_tarski(A_10, k2_zfmisc_1(B_975, A_976)))), inference(resolution, [status(thm)], [c_24, c_13668])).
% 10.15/3.64  tff(c_14337, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0(k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_14282, c_13682])).
% 10.15/3.64  tff(c_14344, plain, (~v1_xboole_0(k2_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_14337])).
% 10.15/3.64  tff(c_13634, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_13631, c_2422])).
% 10.15/3.64  tff(c_14387, plain, (![C_1034, A_1035, B_1036]: (v1_funct_2(C_1034, A_1035, B_1036) | ~v1_partfun1(C_1034, A_1035) | ~v1_funct_1(C_1034) | ~m1_subset_1(C_1034, k1_zfmisc_1(k2_zfmisc_1(A_1035, B_1036))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.15/3.64  tff(c_14862, plain, (![C_1059]: (v1_funct_2(C_1059, '#skF_7', '#skF_8') | ~v1_partfun1(C_1059, '#skF_7') | ~v1_funct_1(C_1059) | ~m1_subset_1(C_1059, k1_zfmisc_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_13631, c_14387])).
% 10.15/3.64  tff(c_14865, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_partfun1('#skF_9', '#skF_7') | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_13634, c_14862])).
% 10.15/3.64  tff(c_14872, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_partfun1('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_611, c_14865])).
% 10.15/3.64  tff(c_14873, plain, (~v1_partfun1('#skF_9', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_2421, c_14872])).
% 10.15/3.64  tff(c_14276, plain, (v1_funct_2('#skF_9', '#skF_7', k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_14242, c_88])).
% 10.15/3.64  tff(c_14300, plain, (v1_funct_2('#skF_9', '#skF_7', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_611, c_14276])).
% 10.15/3.64  tff(c_14273, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k2_relat_1('#skF_9')))) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_14242, c_86])).
% 10.15/3.64  tff(c_14298, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k2_relat_1('#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_611, c_14273])).
% 10.15/3.64  tff(c_15773, plain, (![C_1121, A_1122, B_1123]: (v1_partfun1(C_1121, A_1122) | ~v1_funct_2(C_1121, A_1122, B_1123) | ~v1_funct_1(C_1121) | ~m1_subset_1(C_1121, k1_zfmisc_1(k2_zfmisc_1(A_1122, B_1123))) | v1_xboole_0(B_1123))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.15/3.64  tff(c_15779, plain, (v1_partfun1('#skF_9', '#skF_7') | ~v1_funct_2('#skF_9', '#skF_7', k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | v1_xboole_0(k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_14298, c_15773])).
% 10.15/3.64  tff(c_15808, plain, (v1_partfun1('#skF_9', '#skF_7') | v1_xboole_0(k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_611, c_14300, c_15779])).
% 10.15/3.64  tff(c_15810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14344, c_14873, c_15808])).
% 10.15/3.64  tff(c_15811, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_14337])).
% 10.15/3.64  tff(c_15817, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_15811, c_8])).
% 10.15/3.64  tff(c_15822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13656, c_15817])).
% 10.15/3.64  tff(c_15824, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_13641])).
% 10.15/3.64  tff(c_15836, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15824, c_6])).
% 10.15/3.64  tff(c_15835, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_15824, c_15824, c_34])).
% 10.15/3.64  tff(c_18143, plain, (![C_1322, B_1323]: (r2_hidden('#skF_6'(k1_relat_1(C_1322), B_1323, C_1322), k1_relat_1(C_1322)) | v1_funct_2(C_1322, k1_relat_1(C_1322), B_1323) | ~v1_funct_1(C_1322) | ~v1_relat_1(C_1322))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.15/3.64  tff(c_18173, plain, (![B_1323]: (r2_hidden('#skF_6'('#skF_9', B_1323, '#skF_9'), k1_relat_1('#skF_9')) | v1_funct_2('#skF_9', k1_relat_1('#skF_9'), B_1323) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_15835, c_18143])).
% 10.15/3.64  tff(c_18182, plain, (![B_1324]: (r2_hidden('#skF_6'('#skF_9', B_1324, '#skF_9'), '#skF_9') | v1_funct_2('#skF_9', '#skF_9', B_1324))), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_611, c_15835, c_15835, c_18173])).
% 10.15/3.64  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.15/3.64  tff(c_18185, plain, (![B_1324]: (~v1_xboole_0('#skF_9') | v1_funct_2('#skF_9', '#skF_9', B_1324))), inference(resolution, [status(thm)], [c_18182, c_2])).
% 10.15/3.64  tff(c_18188, plain, (![B_1324]: (v1_funct_2('#skF_9', '#skF_9', B_1324))), inference(demodulation, [status(thm), theory('equality')], [c_15836, c_18185])).
% 10.15/3.64  tff(c_15823, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_13641])).
% 10.15/3.64  tff(c_15927, plain, ('#skF_7'='#skF_9' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_15824, c_15824, c_15823])).
% 10.15/3.64  tff(c_15928, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_15927])).
% 10.15/3.64  tff(c_2749, plain, (![A_299, B_300, D_301]: ('#skF_5'(A_299, B_300, k1_funct_2(A_299, B_300), D_301)=D_301 | ~r2_hidden(D_301, k1_funct_2(A_299, B_300)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_2756, plain, ('#skF_5'('#skF_7', '#skF_8', k1_funct_2('#skF_7', '#skF_8'), '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_106, c_2749])).
% 10.15/3.64  tff(c_2964, plain, (![A_317, B_318, D_319]: (k1_relat_1('#skF_5'(A_317, B_318, k1_funct_2(A_317, B_318), D_319))=A_317 | ~r2_hidden(D_319, k1_funct_2(A_317, B_318)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_3009, plain, (k1_relat_1('#skF_9')='#skF_7' | ~r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2756, c_2964])).
% 10.15/3.64  tff(c_3013, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3009])).
% 10.15/3.64  tff(c_2509, plain, (![A_274]: (m1_subset_1(A_274, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_274), k2_relat_1(A_274)))) | ~v1_funct_1(A_274) | ~v1_relat_1(A_274))), inference(cnfTransformation, [status(thm)], [f_137])).
% 10.15/3.64  tff(c_2527, plain, (![A_274]: (r1_tarski(A_274, k2_zfmisc_1(k1_relat_1(A_274), k2_relat_1(A_274))) | ~v1_funct_1(A_274) | ~v1_relat_1(A_274))), inference(resolution, [status(thm)], [c_2509, c_22])).
% 10.15/3.64  tff(c_3023, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_7', k2_relat_1('#skF_9'))) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3013, c_2527])).
% 10.15/3.64  tff(c_3058, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_7', k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_611, c_3023])).
% 10.15/3.64  tff(c_2463, plain, (![C_267, B_268, A_269]: (v1_xboole_0(C_267) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(B_268, A_269))) | ~v1_xboole_0(A_269))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.15/3.64  tff(c_2478, plain, (![A_10, A_269, B_268]: (v1_xboole_0(A_10) | ~v1_xboole_0(A_269) | ~r1_tarski(A_10, k2_zfmisc_1(B_268, A_269)))), inference(resolution, [status(thm)], [c_24, c_2463])).
% 10.15/3.64  tff(c_5351, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0(k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_3058, c_2478])).
% 10.15/3.64  tff(c_5362, plain, (~v1_xboole_0(k2_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_5351])).
% 10.15/3.64  tff(c_5606, plain, (![C_467, A_468, B_469]: (v1_funct_2(C_467, A_468, B_469) | ~v1_partfun1(C_467, A_468) | ~v1_funct_1(C_467) | ~m1_subset_1(C_467, k1_zfmisc_1(k2_zfmisc_1(A_468, B_469))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.15/3.64  tff(c_5624, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_partfun1('#skF_9', '#skF_7') | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_2422, c_5606])).
% 10.15/3.64  tff(c_5641, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_partfun1('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_611, c_5624])).
% 10.15/3.64  tff(c_5642, plain, (~v1_partfun1('#skF_9', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_2421, c_5641])).
% 10.15/3.64  tff(c_3050, plain, (v1_funct_2('#skF_9', '#skF_7', k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3013, c_88])).
% 10.15/3.64  tff(c_3076, plain, (v1_funct_2('#skF_9', '#skF_7', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_611, c_3050])).
% 10.15/3.64  tff(c_3047, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k2_relat_1('#skF_9')))) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3013, c_86])).
% 10.15/3.64  tff(c_3074, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k2_relat_1('#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_611, c_3047])).
% 10.15/3.64  tff(c_6573, plain, (![C_529, A_530, B_531]: (v1_partfun1(C_529, A_530) | ~v1_funct_2(C_529, A_530, B_531) | ~v1_funct_1(C_529) | ~m1_subset_1(C_529, k1_zfmisc_1(k2_zfmisc_1(A_530, B_531))) | v1_xboole_0(B_531))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.15/3.64  tff(c_6579, plain, (v1_partfun1('#skF_9', '#skF_7') | ~v1_funct_2('#skF_9', '#skF_7', k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | v1_xboole_0(k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_3074, c_6573])).
% 10.15/3.64  tff(c_6608, plain, (v1_partfun1('#skF_9', '#skF_7') | v1_xboole_0(k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_611, c_3076, c_6579])).
% 10.15/3.64  tff(c_6610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5362, c_5642, c_6608])).
% 10.15/3.64  tff(c_6611, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_5351])).
% 10.15/3.64  tff(c_6619, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_6611, c_8])).
% 10.15/3.64  tff(c_2636, plain, (![A_286, B_287]: (r1_tarski(k1_relat_1(A_286), k1_relat_1(B_287)) | ~r1_tarski(A_286, B_287) | ~v1_relat_1(B_287) | ~v1_relat_1(A_286))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.15/3.64  tff(c_2644, plain, (![A_286]: (r1_tarski(k1_relat_1(A_286), k1_xboole_0) | ~r1_tarski(A_286, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_286))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2636])).
% 10.15/3.64  tff(c_2709, plain, (![A_296]: (r1_tarski(k1_relat_1(A_296), k1_xboole_0) | ~r1_tarski(A_296, k1_xboole_0) | ~v1_relat_1(A_296))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_2644])).
% 10.15/3.64  tff(c_2726, plain, (![A_296]: (v1_relat_1(k1_relat_1(A_296)) | ~r1_tarski(A_296, k1_xboole_0) | ~v1_relat_1(A_296))), inference(resolution, [status(thm)], [c_2709, c_200])).
% 10.15/3.64  tff(c_3032, plain, (v1_relat_1('#skF_7') | ~r1_tarski('#skF_9', k1_xboole_0) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3013, c_2726])).
% 10.15/3.64  tff(c_3064, plain, (v1_relat_1('#skF_7') | ~r1_tarski('#skF_9', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_3032])).
% 10.15/3.64  tff(c_3078, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3064])).
% 10.15/3.64  tff(c_6623, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6619, c_3078])).
% 10.15/3.64  tff(c_6657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_6623])).
% 10.15/3.64  tff(c_6659, plain, (r1_tarski('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3064])).
% 10.15/3.64  tff(c_2473, plain, (![C_267]: (v1_xboole_0(C_267) | ~m1_subset_1(C_267, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2463])).
% 10.15/3.64  tff(c_2496, plain, (![C_272]: (v1_xboole_0(C_272) | ~m1_subset_1(C_272, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2473])).
% 10.15/3.64  tff(c_2501, plain, (![A_10]: (v1_xboole_0(A_10) | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_2496])).
% 10.15/3.64  tff(c_2730, plain, (![A_297]: (v1_xboole_0(k1_relat_1(A_297)) | ~r1_tarski(A_297, k1_xboole_0) | ~v1_relat_1(A_297))), inference(resolution, [status(thm)], [c_2709, c_2501])).
% 10.15/3.64  tff(c_2740, plain, (![A_297]: (k1_relat_1(A_297)=k1_xboole_0 | ~r1_tarski(A_297, k1_xboole_0) | ~v1_relat_1(A_297))), inference(resolution, [status(thm)], [c_2730, c_8])).
% 10.15/3.64  tff(c_6663, plain, (k1_relat_1('#skF_9')=k1_xboole_0 | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_6659, c_2740])).
% 10.15/3.64  tff(c_6677, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_3013, c_6663])).
% 10.15/3.64  tff(c_2725, plain, (![A_296]: (v1_xboole_0(k1_relat_1(A_296)) | ~r1_tarski(A_296, k1_xboole_0) | ~v1_relat_1(A_296))), inference(resolution, [status(thm)], [c_2709, c_2501])).
% 10.15/3.64  tff(c_3035, plain, (v1_xboole_0('#skF_7') | ~r1_tarski('#skF_9', k1_xboole_0) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3013, c_2725])).
% 10.15/3.64  tff(c_3066, plain, (v1_xboole_0('#skF_7') | ~r1_tarski('#skF_9', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_3035])).
% 10.15/3.64  tff(c_6660, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3066])).
% 10.15/3.64  tff(c_6738, plain, (~r1_tarski('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6677, c_6660])).
% 10.15/3.64  tff(c_6685, plain, (r1_tarski('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6677, c_6659])).
% 10.15/3.64  tff(c_6790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6738, c_6685])).
% 10.15/3.64  tff(c_6791, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_3066])).
% 10.15/3.64  tff(c_6799, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_6791, c_8])).
% 10.15/3.64  tff(c_6836, plain, (r1_tarski('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6799, c_6659])).
% 10.15/3.64  tff(c_7051, plain, (![A_545]: (v1_xboole_0(A_545) | ~r1_tarski(A_545, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_6799, c_2501])).
% 10.15/3.64  tff(c_7059, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_6836, c_7051])).
% 10.15/3.64  tff(c_6824, plain, (![A_5]: (A_5='#skF_7' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_6799, c_8])).
% 10.15/3.64  tff(c_7065, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_7059, c_6824])).
% 10.15/3.64  tff(c_6826, plain, (![B_9]: (k2_zfmisc_1('#skF_7', B_9)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6799, c_6799, c_20])).
% 10.15/3.64  tff(c_2446, plain, (~r1_tarski(k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_2433])).
% 10.15/3.64  tff(c_6982, plain, (~r1_tarski('#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6826, c_2446])).
% 10.15/3.64  tff(c_7069, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_7065, c_6982])).
% 10.15/3.64  tff(c_7089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_7069])).
% 10.15/3.64  tff(c_7090, plain, (k2_zfmisc_1('#skF_7', '#skF_8')='#skF_9'), inference(splitRight, [status(thm)], [c_2433])).
% 10.15/3.64  tff(c_7122, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0!='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_7090, c_16])).
% 10.15/3.64  tff(c_7148, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_7122])).
% 10.15/3.64  tff(c_7433, plain, (![A_582, B_583, D_584]: ('#skF_5'(A_582, B_583, k1_funct_2(A_582, B_583), D_584)=D_584 | ~r2_hidden(D_584, k1_funct_2(A_582, B_583)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_7440, plain, ('#skF_5'('#skF_7', '#skF_8', k1_funct_2('#skF_7', '#skF_8'), '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_106, c_7433])).
% 10.15/3.64  tff(c_7621, plain, (![A_597, B_598, D_599]: (k1_relat_1('#skF_5'(A_597, B_598, k1_funct_2(A_597, B_598), D_599))=A_597 | ~r2_hidden(D_599, k1_funct_2(A_597, B_598)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_7663, plain, (k1_relat_1('#skF_9')='#skF_7' | ~r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_7440, c_7621])).
% 10.15/3.64  tff(c_7667, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_7663])).
% 10.15/3.64  tff(c_7149, plain, (![A_551]: (m1_subset_1(A_551, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_551), k2_relat_1(A_551)))) | ~v1_funct_1(A_551) | ~v1_relat_1(A_551))), inference(cnfTransformation, [status(thm)], [f_137])).
% 10.15/3.64  tff(c_7167, plain, (![A_551]: (r1_tarski(A_551, k2_zfmisc_1(k1_relat_1(A_551), k2_relat_1(A_551))) | ~v1_funct_1(A_551) | ~v1_relat_1(A_551))), inference(resolution, [status(thm)], [c_7149, c_22])).
% 10.15/3.64  tff(c_7674, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_7', k2_relat_1('#skF_9'))) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_7667, c_7167])).
% 10.15/3.64  tff(c_7707, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_7', k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_611, c_7674])).
% 10.15/3.64  tff(c_7092, plain, (![C_546, B_547, A_548]: (v1_xboole_0(C_546) | ~m1_subset_1(C_546, k1_zfmisc_1(k2_zfmisc_1(B_547, A_548))) | ~v1_xboole_0(A_548))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.15/3.64  tff(c_7107, plain, (![A_10, A_548, B_547]: (v1_xboole_0(A_10) | ~v1_xboole_0(A_548) | ~r1_tarski(A_10, k2_zfmisc_1(B_547, A_548)))), inference(resolution, [status(thm)], [c_24, c_7092])).
% 10.15/3.64  tff(c_7762, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0(k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_7707, c_7107])).
% 10.15/3.64  tff(c_7769, plain, (~v1_xboole_0(k2_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_7762])).
% 10.15/3.64  tff(c_7112, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_7090, c_2422])).
% 10.15/3.64  tff(c_7926, plain, (![C_610, A_611, B_612]: (v1_funct_2(C_610, A_611, B_612) | ~v1_partfun1(C_610, A_611) | ~v1_funct_1(C_610) | ~m1_subset_1(C_610, k1_zfmisc_1(k2_zfmisc_1(A_611, B_612))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.15/3.64  tff(c_8283, plain, (![C_628]: (v1_funct_2(C_628, '#skF_7', '#skF_8') | ~v1_partfun1(C_628, '#skF_7') | ~v1_funct_1(C_628) | ~m1_subset_1(C_628, k1_zfmisc_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_7090, c_7926])).
% 10.15/3.64  tff(c_8286, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_partfun1('#skF_9', '#skF_7') | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_7112, c_8283])).
% 10.15/3.64  tff(c_8293, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_partfun1('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_611, c_8286])).
% 10.15/3.64  tff(c_8294, plain, (~v1_partfun1('#skF_9', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_2421, c_8293])).
% 10.15/3.64  tff(c_7701, plain, (v1_funct_2('#skF_9', '#skF_7', k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_7667, c_88])).
% 10.15/3.64  tff(c_7725, plain, (v1_funct_2('#skF_9', '#skF_7', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_611, c_7701])).
% 10.15/3.64  tff(c_7698, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k2_relat_1('#skF_9')))) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_7667, c_86])).
% 10.15/3.64  tff(c_7723, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k2_relat_1('#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_611, c_7698])).
% 10.15/3.64  tff(c_9460, plain, (![C_708, A_709, B_710]: (v1_partfun1(C_708, A_709) | ~v1_funct_2(C_708, A_709, B_710) | ~v1_funct_1(C_708) | ~m1_subset_1(C_708, k1_zfmisc_1(k2_zfmisc_1(A_709, B_710))) | v1_xboole_0(B_710))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.15/3.64  tff(c_9466, plain, (v1_partfun1('#skF_9', '#skF_7') | ~v1_funct_2('#skF_9', '#skF_7', k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | v1_xboole_0(k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_7723, c_9460])).
% 10.15/3.64  tff(c_9495, plain, (v1_partfun1('#skF_9', '#skF_7') | v1_xboole_0(k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_611, c_7725, c_9466])).
% 10.15/3.64  tff(c_9497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7769, c_8294, c_9495])).
% 10.15/3.64  tff(c_9498, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_7762])).
% 10.15/3.64  tff(c_9504, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_9498, c_8])).
% 10.15/3.64  tff(c_9509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7148, c_9504])).
% 10.15/3.64  tff(c_9511, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_7122])).
% 10.15/3.64  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.15/3.64  tff(c_2434, plain, (![A_263]: (v1_funct_2(A_263, k1_relat_1(A_263), k2_relat_1(A_263)) | ~v1_funct_1(A_263) | ~v1_relat_1(A_263))), inference(cnfTransformation, [status(thm)], [f_137])).
% 10.15/3.64  tff(c_2437, plain, (v1_funct_2(k1_xboole_0, k1_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_2434])).
% 10.15/3.64  tff(c_2442, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_34, c_2437])).
% 10.15/3.64  tff(c_2445, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2442])).
% 10.15/3.64  tff(c_9514, plain, (~v1_funct_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_9511, c_2445])).
% 10.15/3.64  tff(c_9527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_611, c_9514])).
% 10.15/3.64  tff(c_9528, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_2442])).
% 10.15/3.64  tff(c_15825, plain, (v1_funct_2('#skF_9', '#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15824, c_15824, c_15824, c_9528])).
% 10.15/3.64  tff(c_15932, plain, (v1_funct_2('#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_15928, c_15928, c_15928, c_15825])).
% 10.15/3.64  tff(c_15943, plain, (r2_hidden('#skF_8', k1_funct_2('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_15928, c_106])).
% 10.15/3.64  tff(c_15933, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_15928, c_15928, c_15835])).
% 10.15/3.64  tff(c_16124, plain, (![A_1143, B_1144, D_1145]: ('#skF_5'(A_1143, B_1144, k1_funct_2(A_1143, B_1144), D_1145)=D_1145 | ~r2_hidden(D_1145, k1_funct_2(A_1143, B_1144)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_16130, plain, ('#skF_5'('#skF_7', '#skF_8', k1_funct_2('#skF_7', '#skF_8'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_15943, c_16124])).
% 10.15/3.64  tff(c_16379, plain, (![A_1179, B_1180, D_1181]: (k1_relat_1('#skF_5'(A_1179, B_1180, k1_funct_2(A_1179, B_1180), D_1181))=A_1179 | ~r2_hidden(D_1181, k1_funct_2(A_1179, B_1180)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.15/3.64  tff(c_16415, plain, (k1_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_8', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_16130, c_16379])).
% 10.15/3.64  tff(c_16419, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_15943, c_15933, c_16415])).
% 10.15/3.64  tff(c_15941, plain, (~v1_funct_2('#skF_8', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_15928, c_2421])).
% 10.15/3.64  tff(c_16421, plain, (~v1_funct_2('#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16419, c_15941])).
% 10.15/3.64  tff(c_16426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15932, c_16421])).
% 10.15/3.64  tff(c_16427, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_15927])).
% 10.15/3.64  tff(c_16430, plain, (~v1_funct_2('#skF_9', '#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16427, c_2421])).
% 10.15/3.64  tff(c_18193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18188, c_16430])).
% 10.15/3.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.15/3.64  
% 10.15/3.64  Inference rules
% 10.15/3.64  ----------------------
% 10.15/3.64  #Ref     : 0
% 10.15/3.64  #Sup     : 4222
% 10.15/3.64  #Fact    : 0
% 10.15/3.64  #Define  : 0
% 10.15/3.64  #Split   : 82
% 10.15/3.64  #Chain   : 0
% 10.15/3.64  #Close   : 0
% 10.15/3.64  
% 10.15/3.64  Ordering : KBO
% 10.15/3.64  
% 10.15/3.64  Simplification rules
% 10.15/3.64  ----------------------
% 10.15/3.64  #Subsume      : 950
% 10.15/3.64  #Demod        : 3533
% 10.15/3.64  #Tautology    : 1396
% 10.15/3.64  #SimpNegUnit  : 58
% 10.15/3.64  #BackRed      : 396
% 10.15/3.64  
% 10.15/3.64  #Partial instantiations: 0
% 10.15/3.64  #Strategies tried      : 1
% 10.15/3.64  
% 10.15/3.64  Timing (in seconds)
% 10.15/3.64  ----------------------
% 10.15/3.65  Preprocessing        : 0.37
% 10.15/3.65  Parsing              : 0.18
% 10.15/3.65  CNF conversion       : 0.03
% 10.15/3.65  Main loop            : 2.43
% 10.15/3.65  Inferencing          : 0.80
% 10.15/3.65  Reduction            : 0.81
% 10.15/3.65  Demodulation         : 0.57
% 10.15/3.65  BG Simplification    : 0.09
% 10.15/3.65  Subsumption          : 0.56
% 10.15/3.65  Abstraction          : 0.10
% 10.15/3.65  MUC search           : 0.00
% 10.15/3.65  Cooper               : 0.00
% 10.15/3.65  Total                : 2.90
% 10.15/3.65  Index Insertion      : 0.00
% 10.15/3.65  Index Deletion       : 0.00
% 10.15/3.65  Index Matching       : 0.00
% 10.15/3.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
