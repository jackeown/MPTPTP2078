%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0415+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:16 EST 2020

% Result     : Theorem 5.99s
% Output     : CNFRefutation 6.34s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 140 expanded)
%              Number of leaves         :   28 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 269 expanded)
%              Number of equality atoms :   14 (  57 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_46,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(c_24,plain,(
    ! [A_17] : m1_subset_1('#skF_3'(A_17),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( r2_hidden(A_21,B_22)
      | v1_xboole_0(B_22)
      | ~ m1_subset_1(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_118,plain,(
    ! [A_56,C_57,B_58] :
      ( m1_subset_1(A_56,C_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(C_57))
      | ~ r2_hidden(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_129,plain,(
    ! [A_59] :
      ( m1_subset_1(A_59,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_59,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_118])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_137,plain,(
    ! [A_60] :
      ( r1_tarski(A_60,'#skF_4')
      | ~ r2_hidden(A_60,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_129,c_30])).

tff(c_147,plain,(
    ! [A_21] :
      ( r1_tarski(A_21,'#skF_4')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_21,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_137])).

tff(c_177,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_36,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_182,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_177,c_36])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_182])).

tff(c_189,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_127,plain,(
    ! [A_56] :
      ( m1_subset_1(A_56,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_56,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_118])).

tff(c_22,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_52,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_56,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_52])).

tff(c_57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_22])).

tff(c_72,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    r1_tarski('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_72])).

tff(c_93,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_1'(A_46,B_47),A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [B_30,A_29] :
      ( ~ v1_xboole_0(B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_97,plain,(
    ! [A_46,B_47] :
      ( ~ v1_xboole_0(A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_93,c_38])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    k7_setfam_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_562,plain,(
    ! [A_104,D_105,B_106] :
      ( r2_hidden(k3_subset_1(A_104,D_105),B_106)
      | ~ r2_hidden(D_105,k7_setfam_1(A_104,B_106))
      | ~ m1_subset_1(D_105,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(k7_setfam_1(A_104,B_106),k1_zfmisc_1(k1_zfmisc_1(A_104)))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k1_zfmisc_1(A_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_573,plain,(
    ! [D_105] :
      ( r2_hidden(k3_subset_1('#skF_4',D_105),'#skF_5')
      | ~ r2_hidden(D_105,k7_setfam_1('#skF_4','#skF_5'))
      | ~ m1_subset_1(D_105,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_562])).

tff(c_579,plain,(
    ! [D_105] :
      ( r2_hidden(k3_subset_1('#skF_4',D_105),'#skF_5')
      | ~ r2_hidden(D_105,k1_xboole_0)
      | ~ m1_subset_1(D_105,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_573])).

tff(c_593,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_579])).

tff(c_597,plain,(
    ~ r1_tarski(k1_xboole_0,k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_593])).

tff(c_600,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_97,c_597])).

tff(c_604,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_600])).

tff(c_606,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_579])).

tff(c_160,plain,(
    ! [A_64,B_65] :
      ( k7_setfam_1(A_64,k7_setfam_1(A_64,B_65)) = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_165,plain,(
    k7_setfam_1('#skF_4',k7_setfam_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_160])).

tff(c_171,plain,(
    k7_setfam_1('#skF_4',k1_xboole_0) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_165])).

tff(c_4205,plain,(
    ! [A_260,D_261,B_262] :
      ( r2_hidden(k3_subset_1(A_260,D_261),B_262)
      | ~ r2_hidden(D_261,k7_setfam_1(A_260,B_262))
      | ~ m1_subset_1(D_261,k1_zfmisc_1(A_260))
      | ~ m1_subset_1(B_262,k1_zfmisc_1(k1_zfmisc_1(A_260)))
      | ~ r1_tarski(k7_setfam_1(A_260,B_262),k1_zfmisc_1(A_260)) ) ),
    inference(resolution,[status(thm)],[c_32,c_562])).

tff(c_4225,plain,(
    ! [D_261] :
      ( r2_hidden(k3_subset_1('#skF_4',D_261),k1_xboole_0)
      | ~ r2_hidden(D_261,k7_setfam_1('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_261,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
      | ~ r1_tarski('#skF_5',k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_4205])).

tff(c_5086,plain,(
    ! [D_293] :
      ( r2_hidden(k3_subset_1('#skF_4',D_293),k1_xboole_0)
      | ~ r2_hidden(D_293,'#skF_5')
      | ~ m1_subset_1(D_293,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_606,c_171,c_4225])).

tff(c_5118,plain,(
    ! [D_293] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_293,'#skF_5')
      | ~ m1_subset_1(D_293,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5086,c_38])).

tff(c_5142,plain,(
    ! [D_294] :
      ( ~ r2_hidden(D_294,'#skF_5')
      | ~ m1_subset_1(D_294,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_5118])).

tff(c_5313,plain,(
    ! [A_299] : ~ r2_hidden(A_299,'#skF_5') ),
    inference(resolution,[status(thm)],[c_127,c_5142])).

tff(c_5355,plain,(
    ! [A_21] :
      ( v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_21,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_5313])).

tff(c_5397,plain,(
    ! [A_301] : ~ m1_subset_1(A_301,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_5355])).

tff(c_5418,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_24,c_5397])).

%------------------------------------------------------------------------------
