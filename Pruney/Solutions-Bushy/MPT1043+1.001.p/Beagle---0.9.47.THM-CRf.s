%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1043+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:18 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 461 expanded)
%              Number of leaves         :   27 ( 163 expanded)
%              Depth                    :   16
%              Number of atoms          :  218 (1107 expanded)
%              Number of equality atoms :   12 (  58 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => r1_tarski(k5_partfun1(A,B,C),k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( r2_hidden(D,k5_partfun1(A,B,C))
         => ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B)
        & v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => v1_xboole_0(k5_partfun1(A,B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_partfun1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => r2_hidden(C,k1_funct_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(c_28,plain,(
    ~ r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k1_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_1'(A_29,B_30),A_29)
      | r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_29] : r1_tarski(A_29,A_29) ),
    inference(resolution,[status(thm)],[c_54,c_4])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [D_37,A_38,B_39,C_40] :
      ( v1_funct_1(D_37)
      | ~ r2_hidden(D_37,k5_partfun1(A_38,B_39,C_40))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_146,plain,(
    ! [A_67,B_68,C_69,B_70] :
      ( v1_funct_1('#skF_1'(k5_partfun1(A_67,B_68,C_69),B_70))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_1(C_69)
      | r1_tarski(k5_partfun1(A_67,B_68,C_69),B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_148,plain,(
    ! [B_70] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_2','#skF_3','#skF_4'),B_70))
      | ~ v1_funct_1('#skF_4')
      | r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),B_70) ) ),
    inference(resolution,[status(thm)],[c_30,c_146])).

tff(c_151,plain,(
    ! [B_70] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_2','#skF_3','#skF_4'),B_70))
      | r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_148])).

tff(c_70,plain,(
    ! [C_34,B_35,A_36] :
      ( r2_hidden(C_34,B_35)
      | ~ r2_hidden(C_34,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_1,B_2,B_35] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_35)
      | ~ r1_tarski(A_1,B_35)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_120,plain,(
    ! [D_56,A_57,B_58,C_59] :
      ( v1_funct_2(D_56,A_57,B_58)
      | ~ r2_hidden(D_56,k5_partfun1(A_57,B_58,C_59))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_169,plain,(
    ! [A_85,B_83,B_84,C_87,A_86] :
      ( v1_funct_2('#skF_1'(A_85,B_84),A_86,B_83)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_86,B_83)))
      | ~ v1_funct_1(C_87)
      | ~ r1_tarski(A_85,k5_partfun1(A_86,B_83,C_87))
      | r1_tarski(A_85,B_84) ) ),
    inference(resolution,[status(thm)],[c_73,c_120])).

tff(c_171,plain,(
    ! [A_85,B_84] :
      ( v1_funct_2('#skF_1'(A_85,B_84),'#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(A_85,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_85,B_84) ) ),
    inference(resolution,[status(thm)],[c_30,c_169])).

tff(c_174,plain,(
    ! [A_85,B_84] :
      ( v1_funct_2('#skF_1'(A_85,B_84),'#skF_2','#skF_3')
      | ~ r1_tarski(A_85,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_85,B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_171])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( ~ v1_xboole_0(B_19)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_65,plain,(
    ! [A_32,B_33] :
      ( ~ v1_xboole_0(A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_54,c_24])).

tff(c_69,plain,(
    ~ v1_xboole_0(k5_partfun1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_65,c_28])).

tff(c_110,plain,(
    ! [A_51,B_52,C_53] :
      ( v1_xboole_0(k5_partfun1(A_51,B_52,C_53))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_1(C_53)
      | ~ v1_xboole_0(B_52)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_113,plain,
    ( v1_xboole_0(k5_partfun1('#skF_2','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_110])).

tff(c_116,plain,
    ( v1_xboole_0(k5_partfun1('#skF_2','#skF_3','#skF_4'))
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_113])).

tff(c_117,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_116])).

tff(c_118,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_136,plain,(
    ! [D_63,A_64,B_65,C_66] :
      ( m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ r2_hidden(D_63,k5_partfun1(A_64,B_65,C_66))
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_199,plain,(
    ! [A_98,C_95,B_94,B_96,A_97] :
      ( m1_subset_1('#skF_1'(A_97,B_96),k1_zfmisc_1(k2_zfmisc_1(A_98,B_94)))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_98,B_94)))
      | ~ v1_funct_1(C_95)
      | ~ r1_tarski(A_97,k5_partfun1(A_98,B_94,C_95))
      | r1_tarski(A_97,B_96) ) ),
    inference(resolution,[status(thm)],[c_73,c_136])).

tff(c_203,plain,(
    ! [A_97,B_96] :
      ( m1_subset_1('#skF_1'(A_97,B_96),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(A_97,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_97,B_96) ) ),
    inference(resolution,[status(thm)],[c_30,c_199])).

tff(c_208,plain,(
    ! [A_99,B_100] :
      ( m1_subset_1('#skF_1'(A_99,B_100),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ r1_tarski(A_99,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_99,B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_203])).

tff(c_14,plain,(
    ! [B_10,C_11,A_9] :
      ( k1_xboole_0 = B_10
      | r2_hidden(C_11,k1_funct_2(A_9,B_10))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_2(C_11,A_9,B_10)
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_227,plain,(
    ! [A_99,B_100] :
      ( k1_xboole_0 = '#skF_3'
      | r2_hidden('#skF_1'(A_99,B_100),k1_funct_2('#skF_2','#skF_3'))
      | ~ v1_funct_2('#skF_1'(A_99,B_100),'#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_1'(A_99,B_100))
      | ~ r1_tarski(A_99,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_208,c_14])).

tff(c_238,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_8,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    ! [A_22] :
      ( k1_xboole_0 = A_22
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_37,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_33])).

tff(c_38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_8])).

tff(c_241,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_38])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_241])).

tff(c_248,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_1'(A_105,B_106),k1_funct_2('#skF_2','#skF_3'))
      | ~ v1_funct_2('#skF_1'(A_105,B_106),'#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_1'(A_105,B_106))
      | ~ r1_tarski(A_105,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_105,B_106) ) ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_270,plain,(
    ! [A_111] :
      ( ~ v1_funct_2('#skF_1'(A_111,k1_funct_2('#skF_2','#skF_3')),'#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_1'(A_111,k1_funct_2('#skF_2','#skF_3')))
      | ~ r1_tarski(A_111,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_111,k1_funct_2('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_248,c_4])).

tff(c_281,plain,(
    ! [A_112] :
      ( ~ v1_funct_1('#skF_1'(A_112,k1_funct_2('#skF_2','#skF_3')))
      | ~ r1_tarski(A_112,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_112,k1_funct_2('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_174,c_270])).

tff(c_285,plain,
    ( ~ r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k5_partfun1('#skF_2','#skF_3','#skF_4'))
    | r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_151,c_281])).

tff(c_288,plain,(
    r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k1_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_285])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_288])).

tff(c_292,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_22,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_306,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_292,c_22])).

tff(c_291,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_299,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_291,c_22])).

tff(c_315,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_299])).

tff(c_327,plain,(
    ~ r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_315,c_28])).

tff(c_328,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_30])).

tff(c_391,plain,(
    ! [A_127,B_128,C_129,B_130] :
      ( v1_funct_1('#skF_1'(k5_partfun1(A_127,B_128,C_129),B_130))
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ v1_funct_1(C_129)
      | r1_tarski(k5_partfun1(A_127,B_128,C_129),B_130) ) ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_393,plain,(
    ! [B_130] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_3','#skF_3','#skF_4'),B_130))
      | ~ v1_funct_1('#skF_4')
      | r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),B_130) ) ),
    inference(resolution,[status(thm)],[c_328,c_391])).

tff(c_396,plain,(
    ! [B_130] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_3','#skF_3','#skF_4'),B_130))
      | r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_393])).

tff(c_365,plain,(
    ! [D_116,A_117,B_118,C_119] :
      ( v1_funct_2(D_116,A_117,B_118)
      | ~ r2_hidden(D_116,k5_partfun1(A_117,B_118,C_119))
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ v1_funct_1(C_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_414,plain,(
    ! [B_144,C_143,A_146,B_145,A_147] :
      ( v1_funct_2('#skF_1'(A_147,B_144),A_146,B_145)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_146,B_145)))
      | ~ v1_funct_1(C_143)
      | ~ r1_tarski(A_147,k5_partfun1(A_146,B_145,C_143))
      | r1_tarski(A_147,B_144) ) ),
    inference(resolution,[status(thm)],[c_73,c_365])).

tff(c_416,plain,(
    ! [A_147,B_144] :
      ( v1_funct_2('#skF_1'(A_147,B_144),'#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(A_147,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_147,B_144) ) ),
    inference(resolution,[status(thm)],[c_328,c_414])).

tff(c_419,plain,(
    ! [A_147,B_144] :
      ( v1_funct_2('#skF_1'(A_147,B_144),'#skF_3','#skF_3')
      | ~ r1_tarski(A_147,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_147,B_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_416])).

tff(c_382,plain,(
    ! [D_123,A_124,B_125,C_126] :
      ( m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ r2_hidden(D_123,k5_partfun1(A_124,B_125,C_126))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_funct_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_444,plain,(
    ! [B_155,A_154,A_158,C_156,B_157] :
      ( m1_subset_1('#skF_1'(A_158,B_157),k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ v1_funct_1(C_156)
      | ~ r1_tarski(A_158,k5_partfun1(A_154,B_155,C_156))
      | r1_tarski(A_158,B_157) ) ),
    inference(resolution,[status(thm)],[c_73,c_382])).

tff(c_448,plain,(
    ! [A_158,B_157] :
      ( m1_subset_1('#skF_1'(A_158,B_157),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(A_158,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_158,B_157) ) ),
    inference(resolution,[status(thm)],[c_328,c_444])).

tff(c_453,plain,(
    ! [A_159,B_160] :
      ( m1_subset_1('#skF_1'(A_159,B_160),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ r1_tarski(A_159,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_159,B_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_448])).

tff(c_12,plain,(
    ! [C_11,B_10] :
      ( r2_hidden(C_11,k1_funct_2(k1_xboole_0,B_10))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_10)))
      | ~ v1_funct_2(C_11,k1_xboole_0,B_10)
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_338,plain,(
    ! [C_11,B_10] :
      ( r2_hidden(C_11,k1_funct_2('#skF_3',B_10))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_10)))
      | ~ v1_funct_2(C_11,'#skF_3',B_10)
      | ~ v1_funct_1(C_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_306,c_306,c_12])).

tff(c_481,plain,(
    ! [A_161,B_162] :
      ( r2_hidden('#skF_1'(A_161,B_162),k1_funct_2('#skF_3','#skF_3'))
      | ~ v1_funct_2('#skF_1'(A_161,B_162),'#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_1'(A_161,B_162))
      | ~ r1_tarski(A_161,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_161,B_162) ) ),
    inference(resolution,[status(thm)],[c_453,c_338])).

tff(c_504,plain,(
    ! [A_167] :
      ( ~ v1_funct_2('#skF_1'(A_167,k1_funct_2('#skF_3','#skF_3')),'#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_1'(A_167,k1_funct_2('#skF_3','#skF_3')))
      | ~ r1_tarski(A_167,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_167,k1_funct_2('#skF_3','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_481,c_4])).

tff(c_515,plain,(
    ! [A_168] :
      ( ~ v1_funct_1('#skF_1'(A_168,k1_funct_2('#skF_3','#skF_3')))
      | ~ r1_tarski(A_168,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_168,k1_funct_2('#skF_3','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_419,c_504])).

tff(c_519,plain,
    ( ~ r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),k5_partfun1('#skF_3','#skF_3','#skF_4'))
    | r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),k1_funct_2('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_396,c_515])).

tff(c_522,plain,(
    r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_519])).

tff(c_524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_522])).

%------------------------------------------------------------------------------
