%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0374+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:12 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 133 expanded)
%              Number of leaves         :   25 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 303 expanded)
%              Number of equality atoms :   17 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ( A != k1_xboole_0
             => m1_subset_1(k2_tarski(B,C),k1_zfmisc_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_121,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_5'(A_46,B_47),A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden('#skF_5'(A_14,B_15),B_15)
      | r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_133,plain,(
    ! [A_46] : r1_tarski(A_46,A_46) ),
    inference(resolution,[status(thm)],[c_121,c_42])).

tff(c_56,plain,(
    m1_subset_1('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_75,plain,(
    ! [B_34,A_35] :
      ( v1_xboole_0(B_34)
      | ~ m1_subset_1(B_34,A_35)
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_86,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_75])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( r2_hidden(C_5,k1_zfmisc_1(A_1))
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    ! [B_51,A_52] :
      ( m1_subset_1(B_51,A_52)
      | ~ r2_hidden(B_51,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_303,plain,(
    ! [C_85,A_86] :
      ( m1_subset_1(C_85,k1_zfmisc_1(A_86))
      | v1_xboole_0(k1_zfmisc_1(A_86))
      | ~ r1_tarski(C_85,A_86) ) ),
    inference(resolution,[status(thm)],[c_4,c_138])).

tff(c_50,plain,(
    ~ m1_subset_1(k2_tarski('#skF_7','#skF_8'),k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_316,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_6'))
    | ~ r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_303,c_50])).

tff(c_317,plain,(
    ~ r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_54,plain,(
    m1_subset_1('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_5'(A_14,B_15),A_14)
      | r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_213,plain,(
    ! [D_66,B_67,A_68] :
      ( D_66 = B_67
      | D_66 = A_68
      | ~ r2_hidden(D_66,k2_tarski(A_68,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1759,plain,(
    ! [A_262,B_263,B_264] :
      ( '#skF_5'(k2_tarski(A_262,B_263),B_264) = B_263
      | '#skF_5'(k2_tarski(A_262,B_263),B_264) = A_262
      | r1_tarski(k2_tarski(A_262,B_263),B_264) ) ),
    inference(resolution,[status(thm)],[c_44,c_213])).

tff(c_1798,plain,
    ( '#skF_5'(k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_8'
    | '#skF_5'(k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1759,c_317])).

tff(c_1801,plain,(
    '#skF_5'(k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1798])).

tff(c_106,plain,(
    ! [B_44,A_45] :
      ( r2_hidden(B_44,A_45)
      | ~ m1_subset_1(B_44,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_118,plain,(
    ! [A_14,A_45] :
      ( r1_tarski(A_14,A_45)
      | ~ m1_subset_1('#skF_5'(A_14,A_45),A_45)
      | v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_106,c_42])).

tff(c_1817,plain,
    ( r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1801,c_118])).

tff(c_1832,plain,
    ( r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1817])).

tff(c_1834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_317,c_1832])).

tff(c_1835,plain,(
    '#skF_5'(k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1798])).

tff(c_1852,plain,
    ( r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_8','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1835,c_118])).

tff(c_1867,plain,
    ( r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1852])).

tff(c_1869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_317,c_1867])).

tff(c_1870,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_89,plain,(
    ! [C_36,A_37] :
      ( r2_hidden(C_36,k1_zfmisc_1(A_37))
      | ~ r1_tarski(C_36,A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [B_21,A_20] :
      ( ~ v1_xboole_0(B_21)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_93,plain,(
    ! [A_37,C_36] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_37))
      | ~ r1_tarski(C_36,A_37) ) ),
    inference(resolution,[status(thm)],[c_89,c_48])).

tff(c_1879,plain,(
    ! [C_265] : ~ r1_tarski(C_265,'#skF_6') ),
    inference(resolution,[status(thm)],[c_1870,c_93])).

tff(c_1893,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_133,c_1879])).

tff(c_1895,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_46,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1902,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1895,c_46])).

tff(c_1906,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1902])).

%------------------------------------------------------------------------------
