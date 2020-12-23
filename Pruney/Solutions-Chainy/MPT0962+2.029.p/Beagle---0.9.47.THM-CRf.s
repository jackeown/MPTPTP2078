%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:55 EST 2020

% Result     : Theorem 8.77s
% Output     : CNFRefutation 9.16s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 365 expanded)
%              Number of leaves         :   32 ( 133 expanded)
%              Depth                    :   11
%              Number of atoms          :  208 ( 870 expanded)
%              Number of equality atoms :   40 ( 112 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_99,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_71,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_60,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_56,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_32,plain,(
    ! [A_19] :
      ( r1_tarski(A_19,k2_zfmisc_1(k1_relat_1(A_19),k2_relat_1(A_19)))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10662,plain,(
    ! [D_673,C_674,B_675,A_676] :
      ( m1_subset_1(D_673,k1_zfmisc_1(k2_zfmisc_1(C_674,B_675)))
      | ~ r1_tarski(k2_relat_1(D_673),B_675)
      | ~ m1_subset_1(D_673,k1_zfmisc_1(k2_zfmisc_1(C_674,A_676))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_11258,plain,(
    ! [A_722,C_723,B_724,A_725] :
      ( m1_subset_1(A_722,k1_zfmisc_1(k2_zfmisc_1(C_723,B_724)))
      | ~ r1_tarski(k2_relat_1(A_722),B_724)
      | ~ r1_tarski(A_722,k2_zfmisc_1(C_723,A_725)) ) ),
    inference(resolution,[status(thm)],[c_26,c_10662])).

tff(c_11667,plain,(
    ! [A_763,B_764] :
      ( m1_subset_1(A_763,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_763),B_764)))
      | ~ r1_tarski(k2_relat_1(A_763),B_764)
      | ~ v1_relat_1(A_763) ) ),
    inference(resolution,[status(thm)],[c_32,c_11258])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_396,plain,(
    ! [D_100,C_101,B_102,A_103] :
      ( m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1(C_101,B_102)))
      | ~ r1_tarski(k2_relat_1(D_100),B_102)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1(C_101,A_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1133,plain,(
    ! [A_169,C_170,B_171,A_172] :
      ( m1_subset_1(A_169,k1_zfmisc_1(k2_zfmisc_1(C_170,B_171)))
      | ~ r1_tarski(k2_relat_1(A_169),B_171)
      | ~ r1_tarski(A_169,k2_zfmisc_1(C_170,A_172)) ) ),
    inference(resolution,[status(thm)],[c_26,c_396])).

tff(c_1291,plain,(
    ! [A_186,A_187,B_188] :
      ( m1_subset_1(A_186,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ r1_tarski(k2_relat_1(A_186),B_188)
      | ~ r1_tarski(A_186,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1133])).

tff(c_38,plain,(
    ! [A_20,B_21,C_22] :
      ( k1_relset_1(A_20,B_21,C_22) = k1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1518,plain,(
    ! [A_204,B_205,A_206] :
      ( k1_relset_1(A_204,B_205,A_206) = k1_relat_1(A_206)
      | ~ r1_tarski(k2_relat_1(A_206),B_205)
      | ~ r1_tarski(A_206,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1291,c_38])).

tff(c_1542,plain,(
    ! [A_204] :
      ( k1_relset_1(A_204,'#skF_2','#skF_3') = k1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_56,c_1518])).

tff(c_1589,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1542])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1325,plain,(
    ! [A_189,B_190] :
      ( m1_subset_1(A_189,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_189),B_190)))
      | ~ r1_tarski(k2_relat_1(A_189),B_190)
      | ~ v1_relat_1(A_189) ) ),
    inference(resolution,[status(thm)],[c_32,c_1133])).

tff(c_1670,plain,(
    ! [A_217,B_218] :
      ( k1_relset_1(k1_relat_1(A_217),B_218,A_217) = k1_relat_1(A_217)
      | ~ r1_tarski(k2_relat_1(A_217),B_218)
      | ~ v1_relat_1(A_217) ) ),
    inference(resolution,[status(thm)],[c_1325,c_38])).

tff(c_1684,plain,
    ( k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1670])).

tff(c_1696,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1684])).

tff(c_48,plain,(
    ! [B_28,C_29,A_27] :
      ( k1_xboole_0 = B_28
      | v1_funct_2(C_29,A_27,B_28)
      | k1_relset_1(A_27,B_28,C_29) != A_27
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_9726,plain,(
    ! [B_591,A_592] :
      ( k1_xboole_0 = B_591
      | v1_funct_2(A_592,k1_relat_1(A_592),B_591)
      | k1_relset_1(k1_relat_1(A_592),B_591,A_592) != k1_relat_1(A_592)
      | ~ r1_tarski(k2_relat_1(A_592),B_591)
      | ~ v1_relat_1(A_592) ) ),
    inference(resolution,[status(thm)],[c_1325,c_48])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54])).

tff(c_100,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_9741,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_9726,c_100])).

tff(c_9753,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1696,c_9741])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_254,plain,(
    ! [C_67,B_68,A_69] :
      ( r2_hidden(C_67,B_68)
      | ~ r2_hidden(C_67,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_269,plain,(
    ! [A_76,B_77,B_78] :
      ( r2_hidden('#skF_1'(A_76,B_77),B_78)
      | ~ r1_tarski(A_76,B_78)
      | r1_tarski(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_254])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2444,plain,(
    ! [A_280,B_281,B_282,B_283] :
      ( r2_hidden('#skF_1'(A_280,B_281),B_282)
      | ~ r1_tarski(B_283,B_282)
      | ~ r1_tarski(A_280,B_283)
      | r1_tarski(A_280,B_281) ) ),
    inference(resolution,[status(thm)],[c_269,c_2])).

tff(c_2481,plain,(
    ! [A_284,B_285] :
      ( r2_hidden('#skF_1'(A_284,B_285),'#skF_2')
      | ~ r1_tarski(A_284,k2_relat_1('#skF_3'))
      | r1_tarski(A_284,B_285) ) ),
    inference(resolution,[status(thm)],[c_56,c_2444])).

tff(c_2553,plain,(
    ! [A_287,B_288,B_289] :
      ( r2_hidden('#skF_1'(A_287,B_288),B_289)
      | ~ r1_tarski('#skF_2',B_289)
      | ~ r1_tarski(A_287,k2_relat_1('#skF_3'))
      | r1_tarski(A_287,B_288) ) ),
    inference(resolution,[status(thm)],[c_2481,c_2])).

tff(c_22,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_160,plain,(
    ! [C_49,B_50,A_51] :
      ( ~ v1_xboole_0(C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_166,plain,(
    ! [A_10,A_51] :
      ( ~ v1_xboole_0(A_10)
      | ~ r2_hidden(A_51,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_160])).

tff(c_167,plain,(
    ! [A_51] : ~ r2_hidden(A_51,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_2587,plain,(
    ! [A_287,B_288] :
      ( ~ r1_tarski('#skF_2',k1_xboole_0)
      | ~ r1_tarski(A_287,k2_relat_1('#skF_3'))
      | r1_tarski(A_287,B_288) ) ),
    inference(resolution,[status(thm)],[c_2553,c_167])).

tff(c_2639,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2587])).

tff(c_9836,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9753,c_2639])).

tff(c_9903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_9836])).

tff(c_9905,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2587])).

tff(c_165,plain,(
    ! [B_12,A_51,A_11] :
      ( ~ v1_xboole_0(B_12)
      | ~ r2_hidden(A_51,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_26,c_160])).

tff(c_2510,plain,(
    ! [B_12,A_284,B_285] :
      ( ~ v1_xboole_0(B_12)
      | ~ r1_tarski('#skF_2',B_12)
      | ~ r1_tarski(A_284,k2_relat_1('#skF_3'))
      | r1_tarski(A_284,B_285) ) ),
    inference(resolution,[status(thm)],[c_2481,c_165])).

tff(c_2552,plain,(
    ! [B_12] :
      ( ~ v1_xboole_0(B_12)
      | ~ r1_tarski('#skF_2',B_12) ) ),
    inference(splitLeft,[status(thm)],[c_2510])).

tff(c_9910,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_9905,c_2552])).

tff(c_9945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_9910])).

tff(c_9947,plain,(
    ! [A_593,B_594] :
      ( ~ r1_tarski(A_593,k2_relat_1('#skF_3'))
      | r1_tarski(A_593,B_594) ) ),
    inference(splitRight,[status(thm)],[c_2510])).

tff(c_9979,plain,(
    ! [B_595] : r1_tarski(k2_relat_1('#skF_3'),B_595) ),
    inference(resolution,[status(thm)],[c_14,c_9947])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1430,plain,(
    ! [A_197,B_198] :
      ( r1_tarski(A_197,k2_zfmisc_1(k1_relat_1(A_197),B_198))
      | ~ r1_tarski(k2_relat_1(A_197),B_198)
      | ~ v1_relat_1(A_197) ) ),
    inference(resolution,[status(thm)],[c_1325,c_24])).

tff(c_1456,plain,(
    ! [A_197] :
      ( r1_tarski(A_197,k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(A_197),k1_xboole_0)
      | ~ v1_relat_1(A_197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1430])).

tff(c_10001,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_9979,c_1456])).

tff(c_10061,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_10001])).

tff(c_10063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1589,c_10061])).

tff(c_10065,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1542])).

tff(c_187,plain,(
    ! [B_54,A_55,A_56] :
      ( ~ v1_xboole_0(B_54)
      | ~ r2_hidden(A_55,A_56)
      | ~ r1_tarski(A_56,B_54) ) ),
    inference(resolution,[status(thm)],[c_26,c_160])).

tff(c_191,plain,(
    ! [B_57,A_58,B_59] :
      ( ~ v1_xboole_0(B_57)
      | ~ r1_tarski(A_58,B_57)
      | r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_187])).

tff(c_206,plain,(
    ! [B_60,B_61] :
      ( ~ v1_xboole_0(B_60)
      | r1_tarski(B_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_14,c_191])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_221,plain,(
    ! [B_61,B_60] :
      ( B_61 = B_60
      | ~ r1_tarski(B_61,B_60)
      | ~ v1_xboole_0(B_60) ) ),
    inference(resolution,[status(thm)],[c_206,c_10])).

tff(c_10084,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10065,c_221])).

tff(c_10107,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10084])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_289,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_relset_1(A_79,B_80,C_81) = k1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_297,plain,(
    ! [A_79,B_80] : k1_relset_1(A_79,B_80,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_289])).

tff(c_306,plain,(
    ! [A_79,B_80] : k1_relset_1(A_79,B_80,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_297])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    ! [C_29,B_28] :
      ( v1_funct_2(C_29,k1_xboole_0,B_28)
      | k1_relset_1(k1_xboole_0,B_28,C_29) != k1_xboole_0
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_697,plain,(
    ! [C_135,B_136] :
      ( v1_funct_2(C_135,k1_xboole_0,B_136)
      | k1_relset_1(k1_xboole_0,B_136,C_135) != k1_xboole_0
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_46])).

tff(c_706,plain,(
    ! [B_136] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_136)
      | k1_relset_1(k1_xboole_0,B_136,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_697])).

tff(c_711,plain,(
    ! [B_136] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_706])).

tff(c_10148,plain,(
    ! [B_136] : v1_funct_2('#skF_3','#skF_3',B_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10107,c_10107,c_711])).

tff(c_10165,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10107,c_10107,c_36])).

tff(c_10183,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10165,c_100])).

tff(c_10348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10148,c_10183])).

tff(c_10349,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_11685,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11667,c_10349])).

tff(c_11705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_11685])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.77/3.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.77/3.22  
% 8.77/3.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.77/3.22  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.77/3.22  
% 8.77/3.22  %Foreground sorts:
% 8.77/3.22  
% 8.77/3.22  
% 8.77/3.22  %Background operators:
% 8.77/3.22  
% 8.77/3.22  
% 8.77/3.22  %Foreground operators:
% 8.77/3.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.77/3.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.77/3.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.77/3.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.77/3.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.77/3.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.77/3.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.77/3.22  tff('#skF_2', type, '#skF_2': $i).
% 8.77/3.22  tff('#skF_3', type, '#skF_3': $i).
% 8.77/3.22  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.77/3.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.77/3.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.77/3.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.77/3.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.77/3.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.77/3.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.77/3.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.77/3.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.77/3.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.77/3.22  
% 9.16/3.24  tff(f_112, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 9.16/3.24  tff(f_68, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 9.16/3.24  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.16/3.24  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 9.16/3.24  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.16/3.24  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.16/3.24  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.16/3.24  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.16/3.24  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.16/3.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.16/3.24  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 9.16/3.24  tff(f_64, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 9.16/3.24  tff(f_71, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 9.16/3.24  tff(c_60, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.16/3.24  tff(c_56, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.16/3.24  tff(c_32, plain, (![A_19]: (r1_tarski(A_19, k2_zfmisc_1(k1_relat_1(A_19), k2_relat_1(A_19))) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.16/3.24  tff(c_26, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.16/3.24  tff(c_10662, plain, (![D_673, C_674, B_675, A_676]: (m1_subset_1(D_673, k1_zfmisc_1(k2_zfmisc_1(C_674, B_675))) | ~r1_tarski(k2_relat_1(D_673), B_675) | ~m1_subset_1(D_673, k1_zfmisc_1(k2_zfmisc_1(C_674, A_676))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.16/3.24  tff(c_11258, plain, (![A_722, C_723, B_724, A_725]: (m1_subset_1(A_722, k1_zfmisc_1(k2_zfmisc_1(C_723, B_724))) | ~r1_tarski(k2_relat_1(A_722), B_724) | ~r1_tarski(A_722, k2_zfmisc_1(C_723, A_725)))), inference(resolution, [status(thm)], [c_26, c_10662])).
% 9.16/3.24  tff(c_11667, plain, (![A_763, B_764]: (m1_subset_1(A_763, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_763), B_764))) | ~r1_tarski(k2_relat_1(A_763), B_764) | ~v1_relat_1(A_763))), inference(resolution, [status(thm)], [c_32, c_11258])).
% 9.16/3.24  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.16/3.24  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.16/3.24  tff(c_396, plain, (![D_100, C_101, B_102, A_103]: (m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1(C_101, B_102))) | ~r1_tarski(k2_relat_1(D_100), B_102) | ~m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1(C_101, A_103))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.16/3.24  tff(c_1133, plain, (![A_169, C_170, B_171, A_172]: (m1_subset_1(A_169, k1_zfmisc_1(k2_zfmisc_1(C_170, B_171))) | ~r1_tarski(k2_relat_1(A_169), B_171) | ~r1_tarski(A_169, k2_zfmisc_1(C_170, A_172)))), inference(resolution, [status(thm)], [c_26, c_396])).
% 9.16/3.24  tff(c_1291, plain, (![A_186, A_187, B_188]: (m1_subset_1(A_186, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~r1_tarski(k2_relat_1(A_186), B_188) | ~r1_tarski(A_186, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1133])).
% 9.16/3.24  tff(c_38, plain, (![A_20, B_21, C_22]: (k1_relset_1(A_20, B_21, C_22)=k1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.16/3.24  tff(c_1518, plain, (![A_204, B_205, A_206]: (k1_relset_1(A_204, B_205, A_206)=k1_relat_1(A_206) | ~r1_tarski(k2_relat_1(A_206), B_205) | ~r1_tarski(A_206, k1_xboole_0))), inference(resolution, [status(thm)], [c_1291, c_38])).
% 9.16/3.24  tff(c_1542, plain, (![A_204]: (k1_relset_1(A_204, '#skF_2', '#skF_3')=k1_relat_1('#skF_3') | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_56, c_1518])).
% 9.16/3.24  tff(c_1589, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1542])).
% 9.16/3.24  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.16/3.24  tff(c_1325, plain, (![A_189, B_190]: (m1_subset_1(A_189, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_189), B_190))) | ~r1_tarski(k2_relat_1(A_189), B_190) | ~v1_relat_1(A_189))), inference(resolution, [status(thm)], [c_32, c_1133])).
% 9.16/3.24  tff(c_1670, plain, (![A_217, B_218]: (k1_relset_1(k1_relat_1(A_217), B_218, A_217)=k1_relat_1(A_217) | ~r1_tarski(k2_relat_1(A_217), B_218) | ~v1_relat_1(A_217))), inference(resolution, [status(thm)], [c_1325, c_38])).
% 9.16/3.24  tff(c_1684, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1670])).
% 9.16/3.24  tff(c_1696, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1684])).
% 9.16/3.24  tff(c_48, plain, (![B_28, C_29, A_27]: (k1_xboole_0=B_28 | v1_funct_2(C_29, A_27, B_28) | k1_relset_1(A_27, B_28, C_29)!=A_27 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.16/3.24  tff(c_9726, plain, (![B_591, A_592]: (k1_xboole_0=B_591 | v1_funct_2(A_592, k1_relat_1(A_592), B_591) | k1_relset_1(k1_relat_1(A_592), B_591, A_592)!=k1_relat_1(A_592) | ~r1_tarski(k2_relat_1(A_592), B_591) | ~v1_relat_1(A_592))), inference(resolution, [status(thm)], [c_1325, c_48])).
% 9.16/3.24  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.16/3.24  tff(c_54, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.16/3.24  tff(c_62, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54])).
% 9.16/3.24  tff(c_100, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_62])).
% 9.16/3.24  tff(c_9741, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_9726, c_100])).
% 9.16/3.24  tff(c_9753, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1696, c_9741])).
% 9.16/3.24  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.16/3.24  tff(c_254, plain, (![C_67, B_68, A_69]: (r2_hidden(C_67, B_68) | ~r2_hidden(C_67, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.16/3.24  tff(c_269, plain, (![A_76, B_77, B_78]: (r2_hidden('#skF_1'(A_76, B_77), B_78) | ~r1_tarski(A_76, B_78) | r1_tarski(A_76, B_77))), inference(resolution, [status(thm)], [c_6, c_254])).
% 9.16/3.24  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.16/3.24  tff(c_2444, plain, (![A_280, B_281, B_282, B_283]: (r2_hidden('#skF_1'(A_280, B_281), B_282) | ~r1_tarski(B_283, B_282) | ~r1_tarski(A_280, B_283) | r1_tarski(A_280, B_281))), inference(resolution, [status(thm)], [c_269, c_2])).
% 9.16/3.24  tff(c_2481, plain, (![A_284, B_285]: (r2_hidden('#skF_1'(A_284, B_285), '#skF_2') | ~r1_tarski(A_284, k2_relat_1('#skF_3')) | r1_tarski(A_284, B_285))), inference(resolution, [status(thm)], [c_56, c_2444])).
% 9.16/3.24  tff(c_2553, plain, (![A_287, B_288, B_289]: (r2_hidden('#skF_1'(A_287, B_288), B_289) | ~r1_tarski('#skF_2', B_289) | ~r1_tarski(A_287, k2_relat_1('#skF_3')) | r1_tarski(A_287, B_288))), inference(resolution, [status(thm)], [c_2481, c_2])).
% 9.16/3.24  tff(c_22, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.16/3.24  tff(c_160, plain, (![C_49, B_50, A_51]: (~v1_xboole_0(C_49) | ~m1_subset_1(B_50, k1_zfmisc_1(C_49)) | ~r2_hidden(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.16/3.24  tff(c_166, plain, (![A_10, A_51]: (~v1_xboole_0(A_10) | ~r2_hidden(A_51, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_160])).
% 9.16/3.24  tff(c_167, plain, (![A_51]: (~r2_hidden(A_51, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_166])).
% 9.16/3.24  tff(c_2587, plain, (![A_287, B_288]: (~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(A_287, k2_relat_1('#skF_3')) | r1_tarski(A_287, B_288))), inference(resolution, [status(thm)], [c_2553, c_167])).
% 9.16/3.24  tff(c_2639, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2587])).
% 9.16/3.24  tff(c_9836, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9753, c_2639])).
% 9.16/3.24  tff(c_9903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_9836])).
% 9.16/3.24  tff(c_9905, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2587])).
% 9.16/3.24  tff(c_165, plain, (![B_12, A_51, A_11]: (~v1_xboole_0(B_12) | ~r2_hidden(A_51, A_11) | ~r1_tarski(A_11, B_12))), inference(resolution, [status(thm)], [c_26, c_160])).
% 9.16/3.24  tff(c_2510, plain, (![B_12, A_284, B_285]: (~v1_xboole_0(B_12) | ~r1_tarski('#skF_2', B_12) | ~r1_tarski(A_284, k2_relat_1('#skF_3')) | r1_tarski(A_284, B_285))), inference(resolution, [status(thm)], [c_2481, c_165])).
% 9.16/3.24  tff(c_2552, plain, (![B_12]: (~v1_xboole_0(B_12) | ~r1_tarski('#skF_2', B_12))), inference(splitLeft, [status(thm)], [c_2510])).
% 9.16/3.24  tff(c_9910, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_9905, c_2552])).
% 9.16/3.24  tff(c_9945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_9910])).
% 9.16/3.24  tff(c_9947, plain, (![A_593, B_594]: (~r1_tarski(A_593, k2_relat_1('#skF_3')) | r1_tarski(A_593, B_594))), inference(splitRight, [status(thm)], [c_2510])).
% 9.16/3.24  tff(c_9979, plain, (![B_595]: (r1_tarski(k2_relat_1('#skF_3'), B_595))), inference(resolution, [status(thm)], [c_14, c_9947])).
% 9.16/3.24  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.16/3.24  tff(c_1430, plain, (![A_197, B_198]: (r1_tarski(A_197, k2_zfmisc_1(k1_relat_1(A_197), B_198)) | ~r1_tarski(k2_relat_1(A_197), B_198) | ~v1_relat_1(A_197))), inference(resolution, [status(thm)], [c_1325, c_24])).
% 9.16/3.24  tff(c_1456, plain, (![A_197]: (r1_tarski(A_197, k1_xboole_0) | ~r1_tarski(k2_relat_1(A_197), k1_xboole_0) | ~v1_relat_1(A_197))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1430])).
% 9.16/3.24  tff(c_10001, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_9979, c_1456])).
% 9.16/3.24  tff(c_10061, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_10001])).
% 9.16/3.24  tff(c_10063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1589, c_10061])).
% 9.16/3.24  tff(c_10065, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1542])).
% 9.16/3.24  tff(c_187, plain, (![B_54, A_55, A_56]: (~v1_xboole_0(B_54) | ~r2_hidden(A_55, A_56) | ~r1_tarski(A_56, B_54))), inference(resolution, [status(thm)], [c_26, c_160])).
% 9.16/3.24  tff(c_191, plain, (![B_57, A_58, B_59]: (~v1_xboole_0(B_57) | ~r1_tarski(A_58, B_57) | r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_6, c_187])).
% 9.16/3.24  tff(c_206, plain, (![B_60, B_61]: (~v1_xboole_0(B_60) | r1_tarski(B_60, B_61))), inference(resolution, [status(thm)], [c_14, c_191])).
% 9.16/3.24  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.16/3.24  tff(c_221, plain, (![B_61, B_60]: (B_61=B_60 | ~r1_tarski(B_61, B_60) | ~v1_xboole_0(B_60))), inference(resolution, [status(thm)], [c_206, c_10])).
% 9.16/3.24  tff(c_10084, plain, (k1_xboole_0='#skF_3' | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_10065, c_221])).
% 9.16/3.24  tff(c_10107, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10084])).
% 9.16/3.24  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.16/3.24  tff(c_289, plain, (![A_79, B_80, C_81]: (k1_relset_1(A_79, B_80, C_81)=k1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.16/3.24  tff(c_297, plain, (![A_79, B_80]: (k1_relset_1(A_79, B_80, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_289])).
% 9.16/3.24  tff(c_306, plain, (![A_79, B_80]: (k1_relset_1(A_79, B_80, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_297])).
% 9.16/3.24  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.16/3.24  tff(c_46, plain, (![C_29, B_28]: (v1_funct_2(C_29, k1_xboole_0, B_28) | k1_relset_1(k1_xboole_0, B_28, C_29)!=k1_xboole_0 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_28))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.16/3.24  tff(c_697, plain, (![C_135, B_136]: (v1_funct_2(C_135, k1_xboole_0, B_136) | k1_relset_1(k1_xboole_0, B_136, C_135)!=k1_xboole_0 | ~m1_subset_1(C_135, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_46])).
% 9.16/3.24  tff(c_706, plain, (![B_136]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_136) | k1_relset_1(k1_xboole_0, B_136, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_697])).
% 9.16/3.24  tff(c_711, plain, (![B_136]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_136))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_706])).
% 9.16/3.24  tff(c_10148, plain, (![B_136]: (v1_funct_2('#skF_3', '#skF_3', B_136))), inference(demodulation, [status(thm), theory('equality')], [c_10107, c_10107, c_711])).
% 9.16/3.24  tff(c_10165, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10107, c_10107, c_36])).
% 9.16/3.24  tff(c_10183, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10165, c_100])).
% 9.16/3.24  tff(c_10348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10148, c_10183])).
% 9.16/3.24  tff(c_10349, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(splitRight, [status(thm)], [c_62])).
% 9.16/3.24  tff(c_11685, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_11667, c_10349])).
% 9.16/3.24  tff(c_11705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_11685])).
% 9.16/3.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.16/3.24  
% 9.16/3.24  Inference rules
% 9.16/3.24  ----------------------
% 9.16/3.24  #Ref     : 0
% 9.16/3.24  #Sup     : 2793
% 9.16/3.24  #Fact    : 0
% 9.16/3.24  #Define  : 0
% 9.16/3.24  #Split   : 20
% 9.16/3.24  #Chain   : 0
% 9.16/3.24  #Close   : 0
% 9.16/3.24  
% 9.16/3.24  Ordering : KBO
% 9.16/3.24  
% 9.16/3.24  Simplification rules
% 9.16/3.24  ----------------------
% 9.16/3.24  #Subsume      : 1141
% 9.16/3.24  #Demod        : 1728
% 9.16/3.24  #Tautology    : 606
% 9.16/3.24  #SimpNegUnit  : 12
% 9.16/3.24  #BackRed      : 219
% 9.16/3.24  
% 9.16/3.24  #Partial instantiations: 0
% 9.16/3.24  #Strategies tried      : 1
% 9.16/3.24  
% 9.16/3.24  Timing (in seconds)
% 9.16/3.24  ----------------------
% 9.16/3.25  Preprocessing        : 0.34
% 9.16/3.25  Parsing              : 0.18
% 9.16/3.25  CNF conversion       : 0.02
% 9.16/3.25  Main loop            : 2.09
% 9.16/3.25  Inferencing          : 0.54
% 9.16/3.25  Reduction            : 0.59
% 9.16/3.25  Demodulation         : 0.40
% 9.16/3.25  BG Simplification    : 0.06
% 9.16/3.25  Subsumption          : 0.76
% 9.16/3.25  Abstraction          : 0.09
% 9.16/3.25  MUC search           : 0.00
% 9.16/3.25  Cooper               : 0.00
% 9.16/3.25  Total                : 2.48
% 9.16/3.25  Index Insertion      : 0.00
% 9.16/3.25  Index Deletion       : 0.00
% 9.16/3.25  Index Matching       : 0.00
% 9.16/3.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
