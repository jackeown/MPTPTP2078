%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:16 EST 2020

% Result     : Theorem 4.77s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 120 expanded)
%              Number of leaves         :   52 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  127 ( 206 expanded)
%              Number of equality atoms :   57 (  82 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_142,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_131,axiom,(
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

tff(f_113,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_178,plain,(
    ! [A_80,B_81] :
      ( ~ r2_hidden(A_80,B_81)
      | k4_xboole_0(k1_tarski(A_80),B_81) != k1_tarski(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_183,plain,(
    ! [A_80] : ~ r2_hidden(A_80,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_178])).

tff(c_110,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_112,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_114,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_173,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_177,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_114,c_173])).

tff(c_118,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_116,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_267,plain,(
    ! [A_166,B_167,C_168] :
      ( k1_relset_1(A_166,B_167,C_168) = k1_relat_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_271,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_114,c_267])).

tff(c_555,plain,(
    ! [B_275,A_276,C_277] :
      ( k1_xboole_0 = B_275
      | k1_relset_1(A_276,B_275,C_277) = A_276
      | ~ v1_funct_2(C_277,A_276,B_275)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_276,B_275))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_558,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_114,c_555])).

tff(c_561,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_271,c_558])).

tff(c_593,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_561])).

tff(c_96,plain,(
    ! [A_62,B_63] : k2_mcart_1(k4_tarski(A_62,B_63)) = B_63 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_378,plain,(
    ! [A_189,C_190] :
      ( r2_hidden(k4_tarski(A_189,k1_funct_1(C_190,A_189)),C_190)
      | ~ r2_hidden(A_189,k1_relat_1(C_190))
      | ~ v1_funct_1(C_190)
      | ~ v1_relat_1(C_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_78,plain,(
    ! [C_49,A_46,B_47] :
      ( r2_hidden(C_49,A_46)
      | ~ r2_hidden(C_49,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1189,plain,(
    ! [A_727,C_728,A_729] :
      ( r2_hidden(k4_tarski(A_727,k1_funct_1(C_728,A_727)),A_729)
      | ~ m1_subset_1(C_728,k1_zfmisc_1(A_729))
      | ~ r2_hidden(A_727,k1_relat_1(C_728))
      | ~ v1_funct_1(C_728)
      | ~ v1_relat_1(C_728) ) ),
    inference(resolution,[status(thm)],[c_378,c_78])).

tff(c_90,plain,(
    ! [A_59,C_61,B_60] :
      ( k2_mcart_1(A_59) = C_61
      | ~ r2_hidden(A_59,k2_zfmisc_1(B_60,k1_tarski(C_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1209,plain,(
    ! [A_727,C_728,C_61,B_60] :
      ( k2_mcart_1(k4_tarski(A_727,k1_funct_1(C_728,A_727))) = C_61
      | ~ m1_subset_1(C_728,k1_zfmisc_1(k2_zfmisc_1(B_60,k1_tarski(C_61))))
      | ~ r2_hidden(A_727,k1_relat_1(C_728))
      | ~ v1_funct_1(C_728)
      | ~ v1_relat_1(C_728) ) ),
    inference(resolution,[status(thm)],[c_1189,c_90])).

tff(c_1256,plain,(
    ! [C_738,A_739,C_740,B_741] :
      ( k1_funct_1(C_738,A_739) = C_740
      | ~ m1_subset_1(C_738,k1_zfmisc_1(k2_zfmisc_1(B_741,k1_tarski(C_740))))
      | ~ r2_hidden(A_739,k1_relat_1(C_738))
      | ~ v1_funct_1(C_738)
      | ~ v1_relat_1(C_738) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1209])).

tff(c_1258,plain,(
    ! [A_739] :
      ( k1_funct_1('#skF_6',A_739) = '#skF_4'
      | ~ r2_hidden(A_739,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_114,c_1256])).

tff(c_1262,plain,(
    ! [A_742] :
      ( k1_funct_1('#skF_6',A_742) = '#skF_4'
      | ~ r2_hidden(A_742,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_118,c_593,c_1258])).

tff(c_1277,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_112,c_1262])).

tff(c_1284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_1277])).

tff(c_1285,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_561])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k2_enumset1(A_7,A_7,B_8,C_9) = k1_enumset1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12,D_13] : k3_enumset1(A_10,A_10,B_11,C_12,D_13) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [E_18,C_16,D_17,A_14,B_15] : k4_enumset1(A_14,A_14,B_15,C_16,D_17,E_18) = k3_enumset1(A_14,B_15,C_16,D_17,E_18) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] : k5_enumset1(A_19,A_19,B_20,C_21,D_22,E_23,F_24) = k4_enumset1(A_19,B_20,C_21,D_22,E_23,F_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_422,plain,(
    ! [B_248,F_247,E_249,D_243,A_245,C_246,G_244] : k6_enumset1(A_245,A_245,B_248,C_246,D_243,E_249,F_247,G_244) = k5_enumset1(A_245,B_248,C_246,D_243,E_249,F_247,G_244) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [H_41,D_37,J_45,A_34,F_39,B_35,G_40,C_36] : r2_hidden(J_45,k6_enumset1(A_34,B_35,C_36,D_37,J_45,F_39,G_40,H_41)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_470,plain,(
    ! [C_255,G_252,E_251,D_256,F_250,A_254,B_253] : r2_hidden(D_256,k5_enumset1(A_254,B_253,C_255,D_256,E_251,F_250,G_252)) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_32])).

tff(c_487,plain,(
    ! [B_259,A_260,F_261,D_262,C_257,E_258] : r2_hidden(C_257,k4_enumset1(A_260,B_259,C_257,D_262,E_258,F_261)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_470])).

tff(c_504,plain,(
    ! [D_264,E_263,A_267,B_266,C_265] : r2_hidden(B_266,k3_enumset1(A_267,B_266,C_265,D_264,E_263)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_487])).

tff(c_521,plain,(
    ! [A_268,B_269,C_270,D_271] : r2_hidden(A_268,k2_enumset1(A_268,B_269,C_270,D_271)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_504])).

tff(c_538,plain,(
    ! [A_272,B_273,C_274] : r2_hidden(A_272,k1_enumset1(A_272,B_273,C_274)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_521])).

tff(c_562,plain,(
    ! [A_278,B_279] : r2_hidden(A_278,k2_tarski(A_278,B_279)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_538])).

tff(c_575,plain,(
    ! [A_4] : r2_hidden(A_4,k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_562])).

tff(c_1293,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1285,c_575])).

tff(c_1308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_1293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.77/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.80  
% 4.77/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.80  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 4.77/1.80  
% 4.77/1.80  %Foreground sorts:
% 4.77/1.80  
% 4.77/1.80  
% 4.77/1.80  %Background operators:
% 4.77/1.80  
% 4.77/1.80  
% 4.77/1.80  %Foreground operators:
% 4.77/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.77/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.77/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.77/1.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.77/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.77/1.80  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.77/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.77/1.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.77/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.77/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.77/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.77/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.77/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.77/1.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.77/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.77/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.77/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.77/1.80  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.77/1.80  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.77/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.77/1.80  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.77/1.80  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.77/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.77/1.80  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.77/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.77/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.77/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.77/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.77/1.80  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.77/1.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.77/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.77/1.80  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.77/1.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.77/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.77/1.80  
% 4.77/1.82  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.77/1.82  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 4.77/1.82  tff(f_142, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 4.77/1.82  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.77/1.82  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.77/1.82  tff(f_131, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.77/1.82  tff(f_113, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 4.77/1.82  tff(f_95, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 4.77/1.82  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.77/1.82  tff(f_109, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 4.77/1.82  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.77/1.82  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.77/1.82  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.77/1.82  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.77/1.82  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 4.77/1.82  tff(f_41, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 4.77/1.82  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 4.77/1.82  tff(f_78, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 4.77/1.82  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.77/1.82  tff(c_178, plain, (![A_80, B_81]: (~r2_hidden(A_80, B_81) | k4_xboole_0(k1_tarski(A_80), B_81)!=k1_tarski(A_80))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.77/1.82  tff(c_183, plain, (![A_80]: (~r2_hidden(A_80, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_178])).
% 4.77/1.82  tff(c_110, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.77/1.82  tff(c_112, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.77/1.82  tff(c_114, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.77/1.82  tff(c_173, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.77/1.82  tff(c_177, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_114, c_173])).
% 4.77/1.82  tff(c_118, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.77/1.82  tff(c_116, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.77/1.82  tff(c_267, plain, (![A_166, B_167, C_168]: (k1_relset_1(A_166, B_167, C_168)=k1_relat_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.77/1.82  tff(c_271, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_114, c_267])).
% 4.77/1.82  tff(c_555, plain, (![B_275, A_276, C_277]: (k1_xboole_0=B_275 | k1_relset_1(A_276, B_275, C_277)=A_276 | ~v1_funct_2(C_277, A_276, B_275) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_276, B_275))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.77/1.82  tff(c_558, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_114, c_555])).
% 4.77/1.82  tff(c_561, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_271, c_558])).
% 4.77/1.82  tff(c_593, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_561])).
% 4.77/1.82  tff(c_96, plain, (![A_62, B_63]: (k2_mcart_1(k4_tarski(A_62, B_63))=B_63)), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.77/1.82  tff(c_378, plain, (![A_189, C_190]: (r2_hidden(k4_tarski(A_189, k1_funct_1(C_190, A_189)), C_190) | ~r2_hidden(A_189, k1_relat_1(C_190)) | ~v1_funct_1(C_190) | ~v1_relat_1(C_190))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.77/1.82  tff(c_78, plain, (![C_49, A_46, B_47]: (r2_hidden(C_49, A_46) | ~r2_hidden(C_49, B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.77/1.82  tff(c_1189, plain, (![A_727, C_728, A_729]: (r2_hidden(k4_tarski(A_727, k1_funct_1(C_728, A_727)), A_729) | ~m1_subset_1(C_728, k1_zfmisc_1(A_729)) | ~r2_hidden(A_727, k1_relat_1(C_728)) | ~v1_funct_1(C_728) | ~v1_relat_1(C_728))), inference(resolution, [status(thm)], [c_378, c_78])).
% 4.77/1.82  tff(c_90, plain, (![A_59, C_61, B_60]: (k2_mcart_1(A_59)=C_61 | ~r2_hidden(A_59, k2_zfmisc_1(B_60, k1_tarski(C_61))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.77/1.82  tff(c_1209, plain, (![A_727, C_728, C_61, B_60]: (k2_mcart_1(k4_tarski(A_727, k1_funct_1(C_728, A_727)))=C_61 | ~m1_subset_1(C_728, k1_zfmisc_1(k2_zfmisc_1(B_60, k1_tarski(C_61)))) | ~r2_hidden(A_727, k1_relat_1(C_728)) | ~v1_funct_1(C_728) | ~v1_relat_1(C_728))), inference(resolution, [status(thm)], [c_1189, c_90])).
% 4.77/1.82  tff(c_1256, plain, (![C_738, A_739, C_740, B_741]: (k1_funct_1(C_738, A_739)=C_740 | ~m1_subset_1(C_738, k1_zfmisc_1(k2_zfmisc_1(B_741, k1_tarski(C_740)))) | ~r2_hidden(A_739, k1_relat_1(C_738)) | ~v1_funct_1(C_738) | ~v1_relat_1(C_738))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1209])).
% 4.77/1.82  tff(c_1258, plain, (![A_739]: (k1_funct_1('#skF_6', A_739)='#skF_4' | ~r2_hidden(A_739, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_114, c_1256])).
% 4.77/1.82  tff(c_1262, plain, (![A_742]: (k1_funct_1('#skF_6', A_742)='#skF_4' | ~r2_hidden(A_742, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_118, c_593, c_1258])).
% 4.77/1.82  tff(c_1277, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_112, c_1262])).
% 4.77/1.82  tff(c_1284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_1277])).
% 4.77/1.82  tff(c_1285, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_561])).
% 4.77/1.82  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.77/1.82  tff(c_8, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.77/1.82  tff(c_10, plain, (![A_7, B_8, C_9]: (k2_enumset1(A_7, A_7, B_8, C_9)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.77/1.82  tff(c_12, plain, (![A_10, B_11, C_12, D_13]: (k3_enumset1(A_10, A_10, B_11, C_12, D_13)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.77/1.82  tff(c_14, plain, (![E_18, C_16, D_17, A_14, B_15]: (k4_enumset1(A_14, A_14, B_15, C_16, D_17, E_18)=k3_enumset1(A_14, B_15, C_16, D_17, E_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.77/1.82  tff(c_16, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (k5_enumset1(A_19, A_19, B_20, C_21, D_22, E_23, F_24)=k4_enumset1(A_19, B_20, C_21, D_22, E_23, F_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.77/1.82  tff(c_422, plain, (![B_248, F_247, E_249, D_243, A_245, C_246, G_244]: (k6_enumset1(A_245, A_245, B_248, C_246, D_243, E_249, F_247, G_244)=k5_enumset1(A_245, B_248, C_246, D_243, E_249, F_247, G_244))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.77/1.82  tff(c_32, plain, (![H_41, D_37, J_45, A_34, F_39, B_35, G_40, C_36]: (r2_hidden(J_45, k6_enumset1(A_34, B_35, C_36, D_37, J_45, F_39, G_40, H_41)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.77/1.82  tff(c_470, plain, (![C_255, G_252, E_251, D_256, F_250, A_254, B_253]: (r2_hidden(D_256, k5_enumset1(A_254, B_253, C_255, D_256, E_251, F_250, G_252)))), inference(superposition, [status(thm), theory('equality')], [c_422, c_32])).
% 4.77/1.82  tff(c_487, plain, (![B_259, A_260, F_261, D_262, C_257, E_258]: (r2_hidden(C_257, k4_enumset1(A_260, B_259, C_257, D_262, E_258, F_261)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_470])).
% 4.77/1.82  tff(c_504, plain, (![D_264, E_263, A_267, B_266, C_265]: (r2_hidden(B_266, k3_enumset1(A_267, B_266, C_265, D_264, E_263)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_487])).
% 4.77/1.82  tff(c_521, plain, (![A_268, B_269, C_270, D_271]: (r2_hidden(A_268, k2_enumset1(A_268, B_269, C_270, D_271)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_504])).
% 4.77/1.82  tff(c_538, plain, (![A_272, B_273, C_274]: (r2_hidden(A_272, k1_enumset1(A_272, B_273, C_274)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_521])).
% 4.77/1.82  tff(c_562, plain, (![A_278, B_279]: (r2_hidden(A_278, k2_tarski(A_278, B_279)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_538])).
% 4.77/1.82  tff(c_575, plain, (![A_4]: (r2_hidden(A_4, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_562])).
% 4.77/1.82  tff(c_1293, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1285, c_575])).
% 4.77/1.82  tff(c_1308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_1293])).
% 4.77/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.82  
% 4.77/1.82  Inference rules
% 4.77/1.82  ----------------------
% 4.77/1.82  #Ref     : 0
% 4.77/1.82  #Sup     : 266
% 4.77/1.82  #Fact    : 0
% 4.77/1.82  #Define  : 0
% 4.77/1.82  #Split   : 3
% 4.77/1.82  #Chain   : 0
% 4.77/1.82  #Close   : 0
% 4.77/1.82  
% 4.77/1.82  Ordering : KBO
% 4.77/1.82  
% 4.77/1.82  Simplification rules
% 4.77/1.82  ----------------------
% 4.77/1.82  #Subsume      : 37
% 4.77/1.82  #Demod        : 27
% 4.77/1.82  #Tautology    : 53
% 4.77/1.82  #SimpNegUnit  : 4
% 4.77/1.82  #BackRed      : 4
% 4.77/1.82  
% 4.77/1.82  #Partial instantiations: 0
% 4.77/1.82  #Strategies tried      : 1
% 4.77/1.82  
% 4.77/1.82  Timing (in seconds)
% 4.77/1.82  ----------------------
% 4.77/1.83  Preprocessing        : 0.37
% 4.77/1.83  Parsing              : 0.18
% 4.77/1.83  CNF conversion       : 0.03
% 4.77/1.83  Main loop            : 0.66
% 4.77/1.83  Inferencing          : 0.22
% 4.77/1.83  Reduction            : 0.19
% 4.77/1.83  Demodulation         : 0.13
% 4.77/1.83  BG Simplification    : 0.03
% 4.77/1.83  Subsumption          : 0.18
% 4.77/1.83  Abstraction          : 0.04
% 4.77/1.83  MUC search           : 0.00
% 4.77/1.83  Cooper               : 0.00
% 4.77/1.83  Total                : 1.07
% 4.77/1.83  Index Insertion      : 0.00
% 4.77/1.83  Index Deletion       : 0.00
% 4.77/1.83  Index Matching       : 0.00
% 4.77/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
