%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:40 EST 2020

% Result     : Theorem 9.27s
% Output     : CNFRefutation 9.30s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 135 expanded)
%              Number of leaves         :   31 (  62 expanded)
%              Depth                    :   20
%              Number of atoms          :  207 ( 393 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > v1_funct_1 > k7_funct_2 > k6_funct_2 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k6_funct_2,type,(
    k6_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k7_funct_2,type,(
    k7_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A)))
                   => r1_tarski(k5_setfam_1(A,D),k5_setfam_1(A,k6_funct_2(A,B,C,k7_funct_2(A,B,C,D)))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A)))
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(A))
                     => ( m1_setfam_1(D,E)
                       => m1_setfam_1(k6_funct_2(A,B,C,k7_funct_2(A,B,C,D)),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A))) )
     => m1_subset_1(k7_funct_2(A,B,C,D),k1_zfmisc_1(k1_zfmisc_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(B))) )
     => m1_subset_1(k6_funct_2(A,B,C,D),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_45,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_53,plain,(
    r1_tarski('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_45])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(k3_tarski(A_3),B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_121,plain,(
    ! [A_85,C_86,B_87] :
      ( m1_subset_1(A_85,C_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(C_86))
      | ~ r2_hidden(A_85,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_155,plain,(
    ! [A_92,B_93,A_94] :
      ( m1_subset_1(A_92,B_93)
      | ~ r2_hidden(A_92,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(resolution,[status(thm)],[c_20,c_121])).

tff(c_216,plain,(
    ! [A_107,B_108,B_109] :
      ( m1_subset_1('#skF_1'(A_107,B_108),B_109)
      | ~ r1_tarski(A_107,B_109)
      | r1_tarski(k3_tarski(A_107),B_108) ) ),
    inference(resolution,[status(thm)],[c_10,c_155])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_321,plain,(
    ! [A_122,B_123,B_124] :
      ( r1_tarski('#skF_1'(A_122,B_123),B_124)
      | ~ r1_tarski(A_122,k1_zfmisc_1(B_124))
      | r1_tarski(k3_tarski(A_122),B_123) ) ),
    inference(resolution,[status(thm)],[c_216,c_18])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r1_tarski('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(k3_tarski(A_3),B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_346,plain,(
    ! [A_122,B_124] :
      ( ~ r1_tarski(A_122,k1_zfmisc_1(B_124))
      | r1_tarski(k3_tarski(A_122),B_124) ) ),
    inference(resolution,[status(thm)],[c_321,c_8])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_52,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_36,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [B_68,A_69] :
      ( m1_setfam_1(B_68,A_69)
      | ~ r1_tarski(A_69,k3_tarski(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_59,plain,(
    ! [B_68] : m1_setfam_1(B_68,k3_tarski(B_68)) ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_457,plain,(
    ! [C_137,A_138,B_136,E_134,D_135] :
      ( m1_setfam_1(k6_funct_2(A_138,B_136,C_137,k7_funct_2(A_138,B_136,C_137,D_135)),E_134)
      | ~ m1_setfam_1(D_135,E_134)
      | ~ m1_subset_1(E_134,k1_zfmisc_1(A_138))
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k1_zfmisc_1(A_138)))
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_138,B_136)))
      | ~ v1_funct_2(C_137,A_138,B_136)
      | ~ v1_funct_1(C_137)
      | v1_xboole_0(B_136)
      | v1_xboole_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2273,plain,(
    ! [E_274,C_273,A_277,B_276,A_275] :
      ( m1_setfam_1(k6_funct_2(A_275,B_276,C_273,k7_funct_2(A_275,B_276,C_273,A_277)),E_274)
      | ~ m1_setfam_1(A_277,E_274)
      | ~ m1_subset_1(E_274,k1_zfmisc_1(A_275))
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276)))
      | ~ v1_funct_2(C_273,A_275,B_276)
      | ~ v1_funct_1(C_273)
      | v1_xboole_0(B_276)
      | v1_xboole_0(A_275)
      | ~ r1_tarski(A_277,k1_zfmisc_1(A_275)) ) ),
    inference(resolution,[status(thm)],[c_20,c_457])).

tff(c_2303,plain,(
    ! [E_274,A_10,A_277,B_276,A_275] :
      ( m1_setfam_1(k6_funct_2(A_275,B_276,A_10,k7_funct_2(A_275,B_276,A_10,A_277)),E_274)
      | ~ m1_setfam_1(A_277,E_274)
      | ~ m1_subset_1(E_274,k1_zfmisc_1(A_275))
      | ~ v1_funct_2(A_10,A_275,B_276)
      | ~ v1_funct_1(A_10)
      | v1_xboole_0(B_276)
      | v1_xboole_0(A_275)
      | ~ r1_tarski(A_277,k1_zfmisc_1(A_275))
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_275,B_276)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2273])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,k3_tarski(B_7))
      | ~ m1_setfam_1(B_7,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_194,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( m1_subset_1(k7_funct_2(A_102,B_103,C_104,D_105),k1_zfmisc_1(k1_zfmisc_1(B_103)))
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k1_zfmisc_1(A_102)))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ v1_funct_2(C_104,A_102,B_103)
      | ~ v1_funct_1(C_104)
      | v1_xboole_0(B_103)
      | v1_xboole_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_205,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( r1_tarski(k7_funct_2(A_102,B_103,C_104,D_105),k1_zfmisc_1(B_103))
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k1_zfmisc_1(A_102)))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ v1_funct_2(C_104,A_102,B_103)
      | ~ v1_funct_1(C_104)
      | v1_xboole_0(B_103)
      | v1_xboole_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_194,c_18])).

tff(c_290,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( m1_subset_1(k6_funct_2(A_115,B_116,C_117,D_118),k1_zfmisc_1(k1_zfmisc_1(A_115)))
      | ~ m1_subset_1(D_118,k1_zfmisc_1(k1_zfmisc_1(B_116)))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_2(C_117,A_115,B_116)
      | ~ v1_funct_1(C_117)
      | v1_xboole_0(B_116)
      | v1_xboole_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( k5_setfam_1(A_8,B_9) = k3_tarski(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k1_zfmisc_1(A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1867,plain,(
    ! [A_249,B_250,C_251,D_252] :
      ( k5_setfam_1(A_249,k6_funct_2(A_249,B_250,C_251,D_252)) = k3_tarski(k6_funct_2(A_249,B_250,C_251,D_252))
      | ~ m1_subset_1(D_252,k1_zfmisc_1(k1_zfmisc_1(B_250)))
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250)))
      | ~ v1_funct_2(C_251,A_249,B_250)
      | ~ v1_funct_1(C_251)
      | v1_xboole_0(B_250)
      | v1_xboole_0(A_249) ) ),
    inference(resolution,[status(thm)],[c_290,c_16])).

tff(c_3578,plain,(
    ! [A_358,B_359,C_360,A_361] :
      ( k5_setfam_1(A_358,k6_funct_2(A_358,B_359,C_360,A_361)) = k3_tarski(k6_funct_2(A_358,B_359,C_360,A_361))
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1(A_358,B_359)))
      | ~ v1_funct_2(C_360,A_358,B_359)
      | ~ v1_funct_1(C_360)
      | v1_xboole_0(B_359)
      | v1_xboole_0(A_358)
      | ~ r1_tarski(A_361,k1_zfmisc_1(B_359)) ) ),
    inference(resolution,[status(thm)],[c_20,c_1867])).

tff(c_3610,plain,(
    ! [A_361] :
      ( k5_setfam_1('#skF_2',k6_funct_2('#skF_2','#skF_3','#skF_4',A_361)) = k3_tarski(k6_funct_2('#skF_2','#skF_3','#skF_4',A_361))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0('#skF_2')
      | ~ r1_tarski(A_361,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_3578])).

tff(c_3623,plain,(
    ! [A_361] :
      ( k5_setfam_1('#skF_2',k6_funct_2('#skF_2','#skF_3','#skF_4',A_361)) = k3_tarski(k6_funct_2('#skF_2','#skF_3','#skF_4',A_361))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0('#skF_2')
      | ~ r1_tarski(A_361,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_3610])).

tff(c_3625,plain,(
    ! [A_362] :
      ( k5_setfam_1('#skF_2',k6_funct_2('#skF_2','#skF_3','#skF_4',A_362)) = k3_tarski(k6_funct_2('#skF_2','#skF_3','#skF_4',A_362))
      | ~ r1_tarski(A_362,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_3623])).

tff(c_3653,plain,(
    ! [A_102,C_104,D_105] :
      ( k5_setfam_1('#skF_2',k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2(A_102,'#skF_3',C_104,D_105))) = k3_tarski(k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2(A_102,'#skF_3',C_104,D_105)))
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k1_zfmisc_1(A_102)))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,'#skF_3')))
      | ~ v1_funct_2(C_104,A_102,'#skF_3')
      | ~ v1_funct_1(C_104)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_205,c_3625])).

tff(c_3713,plain,(
    ! [A_363,C_364,D_365] :
      ( k5_setfam_1('#skF_2',k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2(A_363,'#skF_3',C_364,D_365))) = k3_tarski(k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2(A_363,'#skF_3',C_364,D_365)))
      | ~ m1_subset_1(D_365,k1_zfmisc_1(k1_zfmisc_1(A_363)))
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(A_363,'#skF_3')))
      | ~ v1_funct_2(C_364,A_363,'#skF_3')
      | ~ v1_funct_1(C_364)
      | v1_xboole_0(A_363) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3653])).

tff(c_3749,plain,(
    ! [C_364] :
      ( k5_setfam_1('#skF_2',k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2('#skF_2','#skF_3',C_364,'#skF_5'))) = k3_tarski(k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2('#skF_2','#skF_3',C_364,'#skF_5')))
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2(C_364,'#skF_2','#skF_3')
      | ~ v1_funct_1(C_364)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_3713])).

tff(c_4163,plain,(
    ! [C_383] :
      ( k5_setfam_1('#skF_2',k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2('#skF_2','#skF_3',C_383,'#skF_5'))) = k3_tarski(k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2('#skF_2','#skF_3',C_383,'#skF_5')))
      | ~ m1_subset_1(C_383,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2(C_383,'#skF_2','#skF_3')
      | ~ v1_funct_1(C_383) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3749])).

tff(c_4206,plain,
    ( k5_setfam_1('#skF_2',k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2('#skF_2','#skF_3','#skF_4','#skF_5'))) = k3_tarski(k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2('#skF_2','#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_4163])).

tff(c_4219,plain,(
    k5_setfam_1('#skF_2',k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2('#skF_2','#skF_3','#skF_4','#skF_5'))) = k3_tarski(k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2('#skF_2','#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_4206])).

tff(c_95,plain,(
    ! [A_81,B_82] :
      ( k5_setfam_1(A_81,B_82) = k3_tarski(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(A_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_104,plain,(
    k5_setfam_1('#skF_2','#skF_5') = k3_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_95])).

tff(c_30,plain,(
    ~ r1_tarski(k5_setfam_1('#skF_2','#skF_5'),k5_setfam_1('#skF_2',k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2('#skF_2','#skF_3','#skF_4','#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_105,plain,(
    ~ r1_tarski(k3_tarski('#skF_5'),k5_setfam_1('#skF_2',k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2('#skF_2','#skF_3','#skF_4','#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_30])).

tff(c_8132,plain,(
    ~ r1_tarski(k3_tarski('#skF_5'),k3_tarski(k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2('#skF_2','#skF_3','#skF_4','#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4219,c_105])).

tff(c_8158,plain,(
    ~ m1_setfam_1(k6_funct_2('#skF_2','#skF_3','#skF_4',k7_funct_2('#skF_2','#skF_3','#skF_4','#skF_5')),k3_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_12,c_8132])).

tff(c_8161,plain,
    ( ~ m1_setfam_1('#skF_5',k3_tarski('#skF_5'))
    | ~ m1_subset_1(k3_tarski('#skF_5'),k1_zfmisc_1('#skF_2'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | ~ r1_tarski('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2303,c_8158])).

tff(c_8173,plain,
    ( ~ m1_subset_1(k3_tarski('#skF_5'),k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_53,c_38,c_36,c_59,c_8161])).

tff(c_8174,plain,(
    ~ m1_subset_1(k3_tarski('#skF_5'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_8173])).

tff(c_8192,plain,(
    ~ r1_tarski(k3_tarski('#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_8174])).

tff(c_8257,plain,(
    ~ r1_tarski('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_346,c_8192])).

tff(c_8274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_8257])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 14:15:27 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.27/3.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.30/3.23  
% 9.30/3.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.30/3.23  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > v1_funct_1 > k7_funct_2 > k6_funct_2 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.30/3.23  
% 9.30/3.23  %Foreground sorts:
% 9.30/3.23  
% 9.30/3.23  
% 9.30/3.23  %Background operators:
% 9.30/3.23  
% 9.30/3.23  
% 9.30/3.23  %Foreground operators:
% 9.30/3.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.30/3.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.30/3.23  tff(k6_funct_2, type, k6_funct_2: ($i * $i * $i * $i) > $i).
% 9.30/3.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.30/3.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.30/3.23  tff('#skF_5', type, '#skF_5': $i).
% 9.30/3.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.30/3.23  tff('#skF_2', type, '#skF_2': $i).
% 9.30/3.23  tff('#skF_3', type, '#skF_3': $i).
% 9.30/3.23  tff(k7_funct_2, type, k7_funct_2: ($i * $i * $i * $i) > $i).
% 9.30/3.23  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 9.30/3.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.30/3.23  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 9.30/3.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.30/3.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.30/3.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.30/3.23  tff('#skF_4', type, '#skF_4': $i).
% 9.30/3.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.30/3.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.30/3.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.30/3.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.30/3.23  
% 9.30/3.25  tff(f_132, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A))) => r1_tarski(k5_setfam_1(A, D), k5_setfam_1(A, k6_funct_2(A, B, C, k7_funct_2(A, B, C, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_funct_2)).
% 9.30/3.25  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.30/3.25  tff(f_38, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 9.30/3.25  tff(f_56, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 9.30/3.25  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.30/3.25  tff(f_42, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 9.30/3.25  tff(f_112, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(A)) => (m1_setfam_1(D, E) => m1_setfam_1(k6_funct_2(A, B, C, k7_funct_2(A, B, C, D)), E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_funct_2)).
% 9.30/3.25  tff(f_88, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A)))) => m1_subset_1(k7_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_funct_2)).
% 9.30/3.25  tff(f_72, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(B)))) => m1_subset_1(k6_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_funct_2)).
% 9.30/3.25  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 9.30/3.25  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.30/3.25  tff(c_45, plain, (![A_66, B_67]: (r1_tarski(A_66, B_67) | ~m1_subset_1(A_66, k1_zfmisc_1(B_67)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.30/3.25  tff(c_53, plain, (r1_tarski('#skF_5', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_45])).
% 9.30/3.25  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(k3_tarski(A_3), B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.30/3.25  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.30/3.25  tff(c_121, plain, (![A_85, C_86, B_87]: (m1_subset_1(A_85, C_86) | ~m1_subset_1(B_87, k1_zfmisc_1(C_86)) | ~r2_hidden(A_85, B_87))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.30/3.25  tff(c_155, plain, (![A_92, B_93, A_94]: (m1_subset_1(A_92, B_93) | ~r2_hidden(A_92, A_94) | ~r1_tarski(A_94, B_93))), inference(resolution, [status(thm)], [c_20, c_121])).
% 9.30/3.25  tff(c_216, plain, (![A_107, B_108, B_109]: (m1_subset_1('#skF_1'(A_107, B_108), B_109) | ~r1_tarski(A_107, B_109) | r1_tarski(k3_tarski(A_107), B_108))), inference(resolution, [status(thm)], [c_10, c_155])).
% 9.30/3.25  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.30/3.25  tff(c_321, plain, (![A_122, B_123, B_124]: (r1_tarski('#skF_1'(A_122, B_123), B_124) | ~r1_tarski(A_122, k1_zfmisc_1(B_124)) | r1_tarski(k3_tarski(A_122), B_123))), inference(resolution, [status(thm)], [c_216, c_18])).
% 9.30/3.25  tff(c_8, plain, (![A_3, B_4]: (~r1_tarski('#skF_1'(A_3, B_4), B_4) | r1_tarski(k3_tarski(A_3), B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.30/3.25  tff(c_346, plain, (![A_122, B_124]: (~r1_tarski(A_122, k1_zfmisc_1(B_124)) | r1_tarski(k3_tarski(A_122), B_124))), inference(resolution, [status(thm)], [c_321, c_8])).
% 9.30/3.25  tff(c_42, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.30/3.25  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.30/3.25  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.30/3.25  tff(c_52, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_45])).
% 9.30/3.25  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.30/3.25  tff(c_36, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.30/3.25  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.30/3.25  tff(c_54, plain, (![B_68, A_69]: (m1_setfam_1(B_68, A_69) | ~r1_tarski(A_69, k3_tarski(B_68)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.30/3.25  tff(c_59, plain, (![B_68]: (m1_setfam_1(B_68, k3_tarski(B_68)))), inference(resolution, [status(thm)], [c_6, c_54])).
% 9.30/3.25  tff(c_457, plain, (![C_137, A_138, B_136, E_134, D_135]: (m1_setfam_1(k6_funct_2(A_138, B_136, C_137, k7_funct_2(A_138, B_136, C_137, D_135)), E_134) | ~m1_setfam_1(D_135, E_134) | ~m1_subset_1(E_134, k1_zfmisc_1(A_138)) | ~m1_subset_1(D_135, k1_zfmisc_1(k1_zfmisc_1(A_138))) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_136))) | ~v1_funct_2(C_137, A_138, B_136) | ~v1_funct_1(C_137) | v1_xboole_0(B_136) | v1_xboole_0(A_138))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.30/3.25  tff(c_2273, plain, (![E_274, C_273, A_277, B_276, A_275]: (m1_setfam_1(k6_funct_2(A_275, B_276, C_273, k7_funct_2(A_275, B_276, C_273, A_277)), E_274) | ~m1_setfam_1(A_277, E_274) | ~m1_subset_1(E_274, k1_zfmisc_1(A_275)) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))) | ~v1_funct_2(C_273, A_275, B_276) | ~v1_funct_1(C_273) | v1_xboole_0(B_276) | v1_xboole_0(A_275) | ~r1_tarski(A_277, k1_zfmisc_1(A_275)))), inference(resolution, [status(thm)], [c_20, c_457])).
% 9.30/3.25  tff(c_2303, plain, (![E_274, A_10, A_277, B_276, A_275]: (m1_setfam_1(k6_funct_2(A_275, B_276, A_10, k7_funct_2(A_275, B_276, A_10, A_277)), E_274) | ~m1_setfam_1(A_277, E_274) | ~m1_subset_1(E_274, k1_zfmisc_1(A_275)) | ~v1_funct_2(A_10, A_275, B_276) | ~v1_funct_1(A_10) | v1_xboole_0(B_276) | v1_xboole_0(A_275) | ~r1_tarski(A_277, k1_zfmisc_1(A_275)) | ~r1_tarski(A_10, k2_zfmisc_1(A_275, B_276)))), inference(resolution, [status(thm)], [c_20, c_2273])).
% 9.30/3.25  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, k3_tarski(B_7)) | ~m1_setfam_1(B_7, A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.30/3.25  tff(c_194, plain, (![A_102, B_103, C_104, D_105]: (m1_subset_1(k7_funct_2(A_102, B_103, C_104, D_105), k1_zfmisc_1(k1_zfmisc_1(B_103))) | ~m1_subset_1(D_105, k1_zfmisc_1(k1_zfmisc_1(A_102))) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~v1_funct_2(C_104, A_102, B_103) | ~v1_funct_1(C_104) | v1_xboole_0(B_103) | v1_xboole_0(A_102))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.30/3.25  tff(c_205, plain, (![A_102, B_103, C_104, D_105]: (r1_tarski(k7_funct_2(A_102, B_103, C_104, D_105), k1_zfmisc_1(B_103)) | ~m1_subset_1(D_105, k1_zfmisc_1(k1_zfmisc_1(A_102))) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~v1_funct_2(C_104, A_102, B_103) | ~v1_funct_1(C_104) | v1_xboole_0(B_103) | v1_xboole_0(A_102))), inference(resolution, [status(thm)], [c_194, c_18])).
% 9.30/3.25  tff(c_290, plain, (![A_115, B_116, C_117, D_118]: (m1_subset_1(k6_funct_2(A_115, B_116, C_117, D_118), k1_zfmisc_1(k1_zfmisc_1(A_115))) | ~m1_subset_1(D_118, k1_zfmisc_1(k1_zfmisc_1(B_116))) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_2(C_117, A_115, B_116) | ~v1_funct_1(C_117) | v1_xboole_0(B_116) | v1_xboole_0(A_115))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.30/3.25  tff(c_16, plain, (![A_8, B_9]: (k5_setfam_1(A_8, B_9)=k3_tarski(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(k1_zfmisc_1(A_8))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.30/3.25  tff(c_1867, plain, (![A_249, B_250, C_251, D_252]: (k5_setfam_1(A_249, k6_funct_2(A_249, B_250, C_251, D_252))=k3_tarski(k6_funct_2(A_249, B_250, C_251, D_252)) | ~m1_subset_1(D_252, k1_zfmisc_1(k1_zfmisc_1(B_250))) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))) | ~v1_funct_2(C_251, A_249, B_250) | ~v1_funct_1(C_251) | v1_xboole_0(B_250) | v1_xboole_0(A_249))), inference(resolution, [status(thm)], [c_290, c_16])).
% 9.30/3.25  tff(c_3578, plain, (![A_358, B_359, C_360, A_361]: (k5_setfam_1(A_358, k6_funct_2(A_358, B_359, C_360, A_361))=k3_tarski(k6_funct_2(A_358, B_359, C_360, A_361)) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1(A_358, B_359))) | ~v1_funct_2(C_360, A_358, B_359) | ~v1_funct_1(C_360) | v1_xboole_0(B_359) | v1_xboole_0(A_358) | ~r1_tarski(A_361, k1_zfmisc_1(B_359)))), inference(resolution, [status(thm)], [c_20, c_1867])).
% 9.30/3.25  tff(c_3610, plain, (![A_361]: (k5_setfam_1('#skF_2', k6_funct_2('#skF_2', '#skF_3', '#skF_4', A_361))=k3_tarski(k6_funct_2('#skF_2', '#skF_3', '#skF_4', A_361)) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | ~r1_tarski(A_361, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_34, c_3578])).
% 9.30/3.25  tff(c_3623, plain, (![A_361]: (k5_setfam_1('#skF_2', k6_funct_2('#skF_2', '#skF_3', '#skF_4', A_361))=k3_tarski(k6_funct_2('#skF_2', '#skF_3', '#skF_4', A_361)) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | ~r1_tarski(A_361, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_3610])).
% 9.30/3.25  tff(c_3625, plain, (![A_362]: (k5_setfam_1('#skF_2', k6_funct_2('#skF_2', '#skF_3', '#skF_4', A_362))=k3_tarski(k6_funct_2('#skF_2', '#skF_3', '#skF_4', A_362)) | ~r1_tarski(A_362, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_3623])).
% 9.30/3.25  tff(c_3653, plain, (![A_102, C_104, D_105]: (k5_setfam_1('#skF_2', k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2(A_102, '#skF_3', C_104, D_105)))=k3_tarski(k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2(A_102, '#skF_3', C_104, D_105))) | ~m1_subset_1(D_105, k1_zfmisc_1(k1_zfmisc_1(A_102))) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, '#skF_3'))) | ~v1_funct_2(C_104, A_102, '#skF_3') | ~v1_funct_1(C_104) | v1_xboole_0('#skF_3') | v1_xboole_0(A_102))), inference(resolution, [status(thm)], [c_205, c_3625])).
% 9.30/3.25  tff(c_3713, plain, (![A_363, C_364, D_365]: (k5_setfam_1('#skF_2', k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2(A_363, '#skF_3', C_364, D_365)))=k3_tarski(k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2(A_363, '#skF_3', C_364, D_365))) | ~m1_subset_1(D_365, k1_zfmisc_1(k1_zfmisc_1(A_363))) | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(A_363, '#skF_3'))) | ~v1_funct_2(C_364, A_363, '#skF_3') | ~v1_funct_1(C_364) | v1_xboole_0(A_363))), inference(negUnitSimplification, [status(thm)], [c_40, c_3653])).
% 9.30/3.25  tff(c_3749, plain, (![C_364]: (k5_setfam_1('#skF_2', k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2('#skF_2', '#skF_3', C_364, '#skF_5')))=k3_tarski(k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2('#skF_2', '#skF_3', C_364, '#skF_5'))) | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(C_364, '#skF_2', '#skF_3') | ~v1_funct_1(C_364) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_3713])).
% 9.30/3.25  tff(c_4163, plain, (![C_383]: (k5_setfam_1('#skF_2', k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2('#skF_2', '#skF_3', C_383, '#skF_5')))=k3_tarski(k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2('#skF_2', '#skF_3', C_383, '#skF_5'))) | ~m1_subset_1(C_383, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(C_383, '#skF_2', '#skF_3') | ~v1_funct_1(C_383))), inference(negUnitSimplification, [status(thm)], [c_42, c_3749])).
% 9.30/3.25  tff(c_4206, plain, (k5_setfam_1('#skF_2', k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')))=k3_tarski(k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_4163])).
% 9.30/3.25  tff(c_4219, plain, (k5_setfam_1('#skF_2', k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')))=k3_tarski(k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_4206])).
% 9.30/3.25  tff(c_95, plain, (![A_81, B_82]: (k5_setfam_1(A_81, B_82)=k3_tarski(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1(A_81))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.30/3.25  tff(c_104, plain, (k5_setfam_1('#skF_2', '#skF_5')=k3_tarski('#skF_5')), inference(resolution, [status(thm)], [c_32, c_95])).
% 9.30/3.25  tff(c_30, plain, (~r1_tarski(k5_setfam_1('#skF_2', '#skF_5'), k5_setfam_1('#skF_2', k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.30/3.25  tff(c_105, plain, (~r1_tarski(k3_tarski('#skF_5'), k5_setfam_1('#skF_2', k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_30])).
% 9.30/3.25  tff(c_8132, plain, (~r1_tarski(k3_tarski('#skF_5'), k3_tarski(k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_4219, c_105])).
% 9.30/3.25  tff(c_8158, plain, (~m1_setfam_1(k6_funct_2('#skF_2', '#skF_3', '#skF_4', k7_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')), k3_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_8132])).
% 9.30/3.25  tff(c_8161, plain, (~m1_setfam_1('#skF_5', k3_tarski('#skF_5')) | ~m1_subset_1(k3_tarski('#skF_5'), k1_zfmisc_1('#skF_2')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | ~r1_tarski('#skF_5', k1_zfmisc_1('#skF_2')) | ~r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2303, c_8158])).
% 9.30/3.25  tff(c_8173, plain, (~m1_subset_1(k3_tarski('#skF_5'), k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_53, c_38, c_36, c_59, c_8161])).
% 9.30/3.25  tff(c_8174, plain, (~m1_subset_1(k3_tarski('#skF_5'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_8173])).
% 9.30/3.25  tff(c_8192, plain, (~r1_tarski(k3_tarski('#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_20, c_8174])).
% 9.30/3.25  tff(c_8257, plain, (~r1_tarski('#skF_5', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_346, c_8192])).
% 9.30/3.25  tff(c_8274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_8257])).
% 9.30/3.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.30/3.25  
% 9.30/3.25  Inference rules
% 9.30/3.25  ----------------------
% 9.30/3.25  #Ref     : 0
% 9.30/3.25  #Sup     : 1810
% 9.30/3.25  #Fact    : 0
% 9.30/3.25  #Define  : 0
% 9.30/3.25  #Split   : 6
% 9.30/3.25  #Chain   : 0
% 9.30/3.25  #Close   : 0
% 9.30/3.25  
% 9.30/3.25  Ordering : KBO
% 9.30/3.25  
% 9.30/3.25  Simplification rules
% 9.30/3.25  ----------------------
% 9.30/3.25  #Subsume      : 54
% 9.30/3.25  #Demod        : 50
% 9.30/3.25  #Tautology    : 51
% 9.30/3.25  #SimpNegUnit  : 21
% 9.30/3.25  #BackRed      : 7
% 9.30/3.25  
% 9.30/3.25  #Partial instantiations: 0
% 9.30/3.25  #Strategies tried      : 1
% 9.30/3.25  
% 9.30/3.25  Timing (in seconds)
% 9.30/3.25  ----------------------
% 9.30/3.25  Preprocessing        : 0.32
% 9.30/3.25  Parsing              : 0.17
% 9.30/3.25  CNF conversion       : 0.02
% 9.30/3.25  Main loop            : 2.18
% 9.30/3.25  Inferencing          : 0.56
% 9.30/3.25  Reduction            : 0.47
% 9.30/3.25  Demodulation         : 0.32
% 9.30/3.25  BG Simplification    : 0.09
% 9.30/3.25  Subsumption          : 0.88
% 9.30/3.25  Abstraction          : 0.15
% 9.30/3.25  MUC search           : 0.00
% 9.30/3.25  Cooper               : 0.00
% 9.30/3.25  Total                : 2.53
% 9.30/3.25  Index Insertion      : 0.00
% 9.30/3.25  Index Deletion       : 0.00
% 9.30/3.25  Index Matching       : 0.00
% 9.30/3.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
