%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:02 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  108 (1593 expanded)
%              Number of leaves         :   32 ( 513 expanded)
%              Depth                    :   15
%              Number of atoms          :  172 (4065 expanded)
%              Number of equality atoms :   37 (1621 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_hidden(D,k5_partfun1(A,B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(c_72,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ~ r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_62,plain,(
    r1_partfun1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_68,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_97,plain,(
    ! [A_58] :
      ( k1_xboole_0 = A_58
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_101,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_97])).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_95,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_103,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_95])).

tff(c_66,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_64,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_218,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_partfun1(C_68,A_69)
      | ~ v1_funct_2(C_68,A_69,B_70)
      | ~ v1_funct_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | v1_xboole_0(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_224,plain,
    ( v1_partfun1('#skF_9','#skF_6')
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_9')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_218])).

tff(c_238,plain,
    ( v1_partfun1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_224])).

tff(c_243,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_102,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_2])).

tff(c_247,plain,(
    '#skF_7' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_243,c_102])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_247])).

tff(c_252,plain,(
    v1_partfun1('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_534,plain,(
    ! [F_155,A_156,B_157,C_158] :
      ( r2_hidden(F_155,k5_partfun1(A_156,B_157,C_158))
      | ~ r1_partfun1(C_158,F_155)
      | ~ v1_partfun1(F_155,A_156)
      | ~ m1_subset_1(F_155,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157)))
      | ~ v1_funct_1(F_155)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157)))
      | ~ v1_funct_1(C_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_538,plain,(
    ! [C_158] :
      ( r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_7',C_158))
      | ~ r1_partfun1(C_158,'#skF_9')
      | ~ v1_partfun1('#skF_9','#skF_6')
      | ~ v1_funct_1('#skF_9')
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1(C_158) ) ),
    inference(resolution,[status(thm)],[c_64,c_534])).

tff(c_556,plain,(
    ! [C_159] :
      ( r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_7',C_159))
      | ~ r1_partfun1(C_159,'#skF_9')
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1(C_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_252,c_538])).

tff(c_562,plain,
    ( r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_7','#skF_8'))
    | ~ r1_partfun1('#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_556])).

tff(c_568,plain,(
    r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_62,c_562])).

tff(c_570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_568])).

tff(c_571,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_609,plain,(
    ! [A_162] :
      ( A_162 = '#skF_6'
      | ~ v1_xboole_0(A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_2])).

tff(c_613,plain,(
    '#skF_6' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_609])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_574,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_571,c_8])).

tff(c_616,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_613,c_574])).

tff(c_572,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_579,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_572])).

tff(c_619,plain,(
    '#skF_7' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_579])).

tff(c_664,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_619,c_613,c_70])).

tff(c_687,plain,(
    ! [B_170,A_171] :
      ( v1_xboole_0(B_170)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(A_171))
      | ~ v1_xboole_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_696,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_664,c_687])).

tff(c_706,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_696])).

tff(c_608,plain,(
    ! [A_1] :
      ( A_1 = '#skF_6'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_2])).

tff(c_614,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_608])).

tff(c_713,plain,(
    '#skF_1' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_706,c_614])).

tff(c_721,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_664])).

tff(c_640,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_613,c_64])).

tff(c_641,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_640])).

tff(c_699,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_641,c_687])).

tff(c_709,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_699])).

tff(c_717,plain,(
    '#skF_1' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_709,c_614])).

tff(c_736,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_717])).

tff(c_738,plain,(
    r1_partfun1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_62])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_573,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_6',B_3) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_571,c_10])).

tff(c_615,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_613,c_573])).

tff(c_723,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_8',B_3) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_713,c_615])).

tff(c_665,plain,(
    ! [A_167] : m1_subset_1(k6_partfun1(A_167),k1_zfmisc_1(k2_zfmisc_1(A_167,A_167))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_669,plain,(
    m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_665])).

tff(c_690,plain,
    ( v1_xboole_0(k6_partfun1('#skF_1'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_669,c_687])).

tff(c_702,plain,(
    v1_xboole_0(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_690])).

tff(c_764,plain,(
    v1_xboole_0(k6_partfun1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_702])).

tff(c_788,plain,(
    ! [A_180] :
      ( A_180 = '#skF_8'
      | ~ v1_xboole_0(A_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_614])).

tff(c_795,plain,(
    k6_partfun1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_764,c_788])).

tff(c_54,plain,(
    ! [A_53] : v1_partfun1(k6_partfun1(A_53),A_53) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_56,plain,(
    ! [A_53] : m1_subset_1(k6_partfun1(A_53),k1_zfmisc_1(k2_zfmisc_1(A_53,A_53))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1079,plain,(
    ! [F_258,A_259,B_260,C_261] :
      ( r2_hidden(F_258,k5_partfun1(A_259,B_260,C_261))
      | ~ r1_partfun1(C_261,F_258)
      | ~ v1_partfun1(F_258,A_259)
      | ~ m1_subset_1(F_258,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260)))
      | ~ v1_funct_1(F_258)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260)))
      | ~ v1_funct_1(C_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1087,plain,(
    ! [A_53,C_261] :
      ( r2_hidden(k6_partfun1(A_53),k5_partfun1(A_53,A_53,C_261))
      | ~ r1_partfun1(C_261,k6_partfun1(A_53))
      | ~ v1_partfun1(k6_partfun1(A_53),A_53)
      | ~ v1_funct_1(k6_partfun1(A_53))
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_53,A_53)))
      | ~ v1_funct_1(C_261) ) ),
    inference(resolution,[status(thm)],[c_56,c_1079])).

tff(c_1094,plain,(
    ! [A_262,C_263] :
      ( r2_hidden(k6_partfun1(A_262),k5_partfun1(A_262,A_262,C_263))
      | ~ r1_partfun1(C_263,k6_partfun1(A_262))
      | ~ v1_funct_1(k6_partfun1(A_262))
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_262,A_262)))
      | ~ v1_funct_1(C_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1087])).

tff(c_1102,plain,(
    ! [C_263] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8',C_263))
      | ~ r1_partfun1(C_263,k6_partfun1('#skF_8'))
      | ~ v1_funct_1(k6_partfun1('#skF_8'))
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8')))
      | ~ v1_funct_1(C_263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_795,c_1094])).

tff(c_1109,plain,(
    ! [C_264] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8',C_264))
      | ~ r1_partfun1(C_264,'#skF_8')
      | ~ m1_subset_1(C_264,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_1(C_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_72,c_795,c_795,c_1102])).

tff(c_585,plain,(
    ~ r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_58])).

tff(c_618,plain,(
    ~ r2_hidden('#skF_9',k5_partfun1('#skF_1','#skF_1','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_613,c_585])).

tff(c_719,plain,(
    ~ r2_hidden('#skF_9',k5_partfun1('#skF_8','#skF_8','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_713,c_618])).

tff(c_811,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_719])).

tff(c_1114,plain,
    ( ~ r1_partfun1('#skF_8','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1109,c_811])).

tff(c_1121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_721,c_738,c_1114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:49:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.63  
% 3.48/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.63  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 3.48/1.63  
% 3.48/1.63  %Foreground sorts:
% 3.48/1.63  
% 3.48/1.63  
% 3.48/1.63  %Background operators:
% 3.48/1.63  
% 3.48/1.63  
% 3.48/1.63  %Foreground operators:
% 3.48/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.48/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.48/1.63  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 3.48/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.48/1.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.48/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.48/1.63  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.48/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.63  tff('#skF_9', type, '#skF_9': $i).
% 3.48/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.63  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.48/1.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.48/1.63  tff('#skF_8', type, '#skF_8': $i).
% 3.48/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.48/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.48/1.63  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 3.48/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.48/1.63  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.48/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.63  
% 3.48/1.65  tff(f_104, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_hidden(D, k5_partfun1(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_2)).
% 3.48/1.65  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 3.48/1.65  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.48/1.65  tff(f_58, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.48/1.65  tff(f_79, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_partfun1)).
% 3.48/1.65  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.48/1.65  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.48/1.65  tff(f_83, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.48/1.65  tff(c_72, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.48/1.65  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.65  tff(c_58, plain, (~r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.48/1.65  tff(c_62, plain, (r1_partfun1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.48/1.65  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.48/1.65  tff(c_68, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.48/1.65  tff(c_97, plain, (![A_58]: (k1_xboole_0=A_58 | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.65  tff(c_101, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_97])).
% 3.48/1.65  tff(c_60, plain, (k1_xboole_0='#skF_6' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.48/1.65  tff(c_95, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_60])).
% 3.48/1.65  tff(c_103, plain, ('#skF_7'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_95])).
% 3.48/1.65  tff(c_66, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.48/1.65  tff(c_64, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.48/1.65  tff(c_218, plain, (![C_68, A_69, B_70]: (v1_partfun1(C_68, A_69) | ~v1_funct_2(C_68, A_69, B_70) | ~v1_funct_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | v1_xboole_0(B_70))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.48/1.65  tff(c_224, plain, (v1_partfun1('#skF_9', '#skF_6') | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | ~v1_funct_1('#skF_9') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_64, c_218])).
% 3.48/1.65  tff(c_238, plain, (v1_partfun1('#skF_9', '#skF_6') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_224])).
% 3.48/1.65  tff(c_243, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_238])).
% 3.48/1.65  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.65  tff(c_102, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_2])).
% 3.48/1.65  tff(c_247, plain, ('#skF_7'='#skF_1'), inference(resolution, [status(thm)], [c_243, c_102])).
% 3.48/1.65  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_247])).
% 3.48/1.65  tff(c_252, plain, (v1_partfun1('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_238])).
% 3.48/1.65  tff(c_534, plain, (![F_155, A_156, B_157, C_158]: (r2_hidden(F_155, k5_partfun1(A_156, B_157, C_158)) | ~r1_partfun1(C_158, F_155) | ~v1_partfun1(F_155, A_156) | ~m1_subset_1(F_155, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))) | ~v1_funct_1(F_155) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))) | ~v1_funct_1(C_158))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.48/1.65  tff(c_538, plain, (![C_158]: (r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_7', C_158)) | ~r1_partfun1(C_158, '#skF_9') | ~v1_partfun1('#skF_9', '#skF_6') | ~v1_funct_1('#skF_9') | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1(C_158))), inference(resolution, [status(thm)], [c_64, c_534])).
% 3.48/1.65  tff(c_556, plain, (![C_159]: (r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_7', C_159)) | ~r1_partfun1(C_159, '#skF_9') | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1(C_159))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_252, c_538])).
% 3.48/1.65  tff(c_562, plain, (r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~r1_partfun1('#skF_8', '#skF_9') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_556])).
% 3.48/1.65  tff(c_568, plain, (r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_62, c_562])).
% 3.48/1.65  tff(c_570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_568])).
% 3.48/1.65  tff(c_571, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_60])).
% 3.48/1.65  tff(c_609, plain, (![A_162]: (A_162='#skF_6' | ~v1_xboole_0(A_162))), inference(demodulation, [status(thm), theory('equality')], [c_571, c_2])).
% 3.48/1.65  tff(c_613, plain, ('#skF_6'='#skF_1'), inference(resolution, [status(thm)], [c_4, c_609])).
% 3.48/1.65  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.65  tff(c_574, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_571, c_571, c_8])).
% 3.48/1.65  tff(c_616, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_613, c_613, c_574])).
% 3.48/1.65  tff(c_572, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_60])).
% 3.48/1.65  tff(c_579, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_571, c_572])).
% 3.48/1.65  tff(c_619, plain, ('#skF_7'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_613, c_579])).
% 3.48/1.65  tff(c_664, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_616, c_619, c_613, c_70])).
% 3.48/1.65  tff(c_687, plain, (![B_170, A_171]: (v1_xboole_0(B_170) | ~m1_subset_1(B_170, k1_zfmisc_1(A_171)) | ~v1_xboole_0(A_171))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.48/1.65  tff(c_696, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_664, c_687])).
% 3.48/1.65  tff(c_706, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_696])).
% 3.48/1.65  tff(c_608, plain, (![A_1]: (A_1='#skF_6' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_571, c_2])).
% 3.48/1.65  tff(c_614, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_613, c_608])).
% 3.48/1.65  tff(c_713, plain, ('#skF_1'='#skF_8'), inference(resolution, [status(thm)], [c_706, c_614])).
% 3.48/1.65  tff(c_721, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_713, c_664])).
% 3.48/1.65  tff(c_640, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_619, c_613, c_64])).
% 3.48/1.65  tff(c_641, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_616, c_640])).
% 3.48/1.65  tff(c_699, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_641, c_687])).
% 3.48/1.65  tff(c_709, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_699])).
% 3.48/1.65  tff(c_717, plain, ('#skF_1'='#skF_9'), inference(resolution, [status(thm)], [c_709, c_614])).
% 3.48/1.65  tff(c_736, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_713, c_717])).
% 3.48/1.65  tff(c_738, plain, (r1_partfun1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_736, c_62])).
% 3.48/1.65  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.65  tff(c_573, plain, (![B_3]: (k2_zfmisc_1('#skF_6', B_3)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_571, c_571, c_10])).
% 3.48/1.65  tff(c_615, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_613, c_613, c_573])).
% 3.48/1.65  tff(c_723, plain, (![B_3]: (k2_zfmisc_1('#skF_8', B_3)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_713, c_713, c_615])).
% 3.48/1.65  tff(c_665, plain, (![A_167]: (m1_subset_1(k6_partfun1(A_167), k1_zfmisc_1(k2_zfmisc_1(A_167, A_167))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.48/1.65  tff(c_669, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_615, c_665])).
% 3.48/1.65  tff(c_690, plain, (v1_xboole_0(k6_partfun1('#skF_1')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_669, c_687])).
% 3.48/1.65  tff(c_702, plain, (v1_xboole_0(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_690])).
% 3.48/1.65  tff(c_764, plain, (v1_xboole_0(k6_partfun1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_713, c_702])).
% 3.48/1.65  tff(c_788, plain, (![A_180]: (A_180='#skF_8' | ~v1_xboole_0(A_180))), inference(demodulation, [status(thm), theory('equality')], [c_713, c_614])).
% 3.48/1.65  tff(c_795, plain, (k6_partfun1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_764, c_788])).
% 3.48/1.65  tff(c_54, plain, (![A_53]: (v1_partfun1(k6_partfun1(A_53), A_53))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.48/1.65  tff(c_56, plain, (![A_53]: (m1_subset_1(k6_partfun1(A_53), k1_zfmisc_1(k2_zfmisc_1(A_53, A_53))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.48/1.65  tff(c_1079, plain, (![F_258, A_259, B_260, C_261]: (r2_hidden(F_258, k5_partfun1(A_259, B_260, C_261)) | ~r1_partfun1(C_261, F_258) | ~v1_partfun1(F_258, A_259) | ~m1_subset_1(F_258, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))) | ~v1_funct_1(F_258) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))) | ~v1_funct_1(C_261))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.48/1.65  tff(c_1087, plain, (![A_53, C_261]: (r2_hidden(k6_partfun1(A_53), k5_partfun1(A_53, A_53, C_261)) | ~r1_partfun1(C_261, k6_partfun1(A_53)) | ~v1_partfun1(k6_partfun1(A_53), A_53) | ~v1_funct_1(k6_partfun1(A_53)) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_53, A_53))) | ~v1_funct_1(C_261))), inference(resolution, [status(thm)], [c_56, c_1079])).
% 3.48/1.65  tff(c_1094, plain, (![A_262, C_263]: (r2_hidden(k6_partfun1(A_262), k5_partfun1(A_262, A_262, C_263)) | ~r1_partfun1(C_263, k6_partfun1(A_262)) | ~v1_funct_1(k6_partfun1(A_262)) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_262, A_262))) | ~v1_funct_1(C_263))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1087])).
% 3.48/1.65  tff(c_1102, plain, (![C_263]: (r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', C_263)) | ~r1_partfun1(C_263, k6_partfun1('#skF_8')) | ~v1_funct_1(k6_partfun1('#skF_8')) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8'))) | ~v1_funct_1(C_263))), inference(superposition, [status(thm), theory('equality')], [c_795, c_1094])).
% 3.48/1.65  tff(c_1109, plain, (![C_264]: (r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', C_264)) | ~r1_partfun1(C_264, '#skF_8') | ~m1_subset_1(C_264, k1_zfmisc_1('#skF_8')) | ~v1_funct_1(C_264))), inference(demodulation, [status(thm), theory('equality')], [c_723, c_72, c_795, c_795, c_1102])).
% 3.48/1.65  tff(c_585, plain, (~r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_579, c_58])).
% 3.48/1.65  tff(c_618, plain, (~r2_hidden('#skF_9', k5_partfun1('#skF_1', '#skF_1', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_613, c_613, c_585])).
% 3.48/1.65  tff(c_719, plain, (~r2_hidden('#skF_9', k5_partfun1('#skF_8', '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_713, c_713, c_618])).
% 3.48/1.65  tff(c_811, plain, (~r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_736, c_719])).
% 3.48/1.65  tff(c_1114, plain, (~r1_partfun1('#skF_8', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_1109, c_811])).
% 3.48/1.65  tff(c_1121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_721, c_738, c_1114])).
% 3.48/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.65  
% 3.48/1.65  Inference rules
% 3.48/1.65  ----------------------
% 3.48/1.65  #Ref     : 0
% 3.48/1.65  #Sup     : 233
% 3.48/1.65  #Fact    : 0
% 3.48/1.65  #Define  : 0
% 3.48/1.65  #Split   : 5
% 3.48/1.65  #Chain   : 0
% 3.48/1.65  #Close   : 0
% 3.48/1.65  
% 3.48/1.65  Ordering : KBO
% 3.48/1.65  
% 3.48/1.65  Simplification rules
% 3.48/1.65  ----------------------
% 3.48/1.65  #Subsume      : 13
% 3.48/1.65  #Demod        : 228
% 3.48/1.65  #Tautology    : 96
% 3.48/1.65  #SimpNegUnit  : 3
% 3.48/1.65  #BackRed      : 34
% 3.48/1.65  
% 3.48/1.65  #Partial instantiations: 0
% 3.48/1.65  #Strategies tried      : 1
% 3.48/1.65  
% 3.48/1.65  Timing (in seconds)
% 3.48/1.65  ----------------------
% 3.48/1.65  Preprocessing        : 0.36
% 3.48/1.65  Parsing              : 0.18
% 3.48/1.65  CNF conversion       : 0.03
% 3.48/1.66  Main loop            : 0.47
% 3.48/1.66  Inferencing          : 0.18
% 3.48/1.66  Reduction            : 0.15
% 3.48/1.66  Demodulation         : 0.11
% 3.48/1.66  BG Simplification    : 0.03
% 3.48/1.66  Subsumption          : 0.07
% 3.48/1.66  Abstraction          : 0.03
% 3.48/1.66  MUC search           : 0.00
% 3.48/1.66  Cooper               : 0.00
% 3.85/1.66  Total                : 0.87
% 3.85/1.66  Index Insertion      : 0.00
% 3.85/1.66  Index Deletion       : 0.00
% 3.85/1.66  Index Matching       : 0.00
% 3.85/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
