%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0373+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:12 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   59 (  91 expanded)
%              Number of leaves         :   24 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 ( 176 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ( A != k1_xboole_0
         => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_5'(A_13,B_14),A_13)
      | r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_128,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden('#skF_5'(A_46,B_47),B_47)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_141,plain,(
    ! [A_13] : r1_tarski(A_13,A_13) ),
    inference(resolution,[status(thm)],[c_38,c_128])).

tff(c_48,plain,(
    m1_subset_1('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_63,plain,(
    ! [B_28,A_29] :
      ( v1_xboole_0(B_28)
      | ~ m1_subset_1(B_28,A_29)
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_67,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_63])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_28,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_145,plain,(
    ! [B_49,A_50] :
      ( m1_subset_1(B_49,A_50)
      | ~ r2_hidden(B_49,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_260,plain,(
    ! [C_69,A_70] :
      ( m1_subset_1(C_69,k1_zfmisc_1(A_70))
      | v1_xboole_0(k1_zfmisc_1(A_70))
      | ~ r1_tarski(C_69,A_70) ) ),
    inference(resolution,[status(thm)],[c_16,c_145])).

tff(c_44,plain,(
    ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_268,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_6'))
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_260,c_44])).

tff(c_269,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_112,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_5'(A_42,B_43),A_42)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    ! [A_1,B_43] :
      ( '#skF_5'(k1_tarski(A_1),B_43) = A_1
      | r1_tarski(k1_tarski(A_1),B_43) ) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_276,plain,(
    '#skF_5'(k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_125,c_269])).

tff(c_36,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden('#skF_5'(A_13,B_14),B_14)
      | r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_287,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_36])).

tff(c_299,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_287])).

tff(c_317,plain,
    ( ~ m1_subset_1('#skF_7','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_299])).

tff(c_320,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_317])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_320])).

tff(c_323,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_69,plain,(
    ! [C_30,A_31] :
      ( r2_hidden(C_30,k1_zfmisc_1(A_31))
      | ~ r1_tarski(C_30,A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,(
    ! [B_20,A_19] :
      ( ~ v1_xboole_0(B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_73,plain,(
    ! [A_31,C_30] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_31))
      | ~ r1_tarski(C_30,A_31) ) ),
    inference(resolution,[status(thm)],[c_69,c_42])).

tff(c_335,plain,(
    ! [C_73] : ~ r1_tarski(C_73,'#skF_6') ),
    inference(resolution,[status(thm)],[c_323,c_73])).

tff(c_348,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_141,c_335])).

tff(c_350,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_40,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_357,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_350,c_40])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_357])).

%------------------------------------------------------------------------------
