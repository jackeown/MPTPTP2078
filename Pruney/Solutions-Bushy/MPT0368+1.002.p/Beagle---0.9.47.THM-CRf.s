%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0368+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:11 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 193 expanded)
%              Number of leaves         :   21 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 462 expanded)
%              Number of equality atoms :   12 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_34,plain,(
    ! [A_15] : m1_subset_1('#skF_4'(A_15),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_47,plain,(
    ! [C_25] :
      ( r2_hidden(C_25,'#skF_6')
      | ~ m1_subset_1(C_25,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    ! [B_18,A_17] :
      ( ~ v1_xboole_0(B_18)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_51,plain,(
    ! [C_25] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_25,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_47,c_36])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_53,plain,(
    ! [B_26,A_27] :
      ( v1_xboole_0(B_26)
      | ~ m1_subset_1(B_26,A_27)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_56,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_53])).

tff(c_62,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_56])).

tff(c_38,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ v1_xboole_0(B_9)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    ! [C_20] :
      ( r2_hidden(C_20,'#skF_6')
      | ~ m1_subset_1(C_20,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_81,plain,(
    ! [B_37,A_38] :
      ( m1_subset_1(B_37,A_38)
      | ~ r2_hidden(B_37,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_87,plain,(
    ! [C_20] :
      ( m1_subset_1(C_20,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_20,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_81])).

tff(c_92,plain,(
    ! [C_39] :
      ( m1_subset_1(C_39,'#skF_6')
      | ~ m1_subset_1(C_39,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_87])).

tff(c_101,plain,(
    ! [B_9] :
      ( m1_subset_1(B_9,'#skF_6')
      | ~ v1_xboole_0(B_9)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_92])).

tff(c_107,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_145,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_3'(A_46,B_47),A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ r2_hidden(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_293,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1('#skF_3'(A_78,B_79),A_78)
      | v1_xboole_0(A_78)
      | r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_145,c_20])).

tff(c_129,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden('#skF_3'(A_44,B_45),B_45)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_144,plain,(
    ! [A_44] :
      ( r1_tarski(A_44,'#skF_6')
      | ~ m1_subset_1('#skF_3'(A_44,'#skF_6'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_129])).

tff(c_297,plain,
    ( v1_xboole_0('#skF_5')
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_293,c_144])).

tff(c_307,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_297])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_316,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_307,c_2])).

tff(c_321,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_316])).

tff(c_108,plain,(
    ! [B_40,A_41] :
      ( r2_hidden(B_40,A_41)
      | ~ m1_subset_1(B_40,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_348,plain,(
    ! [B_83,A_84] :
      ( r1_tarski(B_83,A_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84))
      | v1_xboole_0(k1_zfmisc_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_108,c_8])).

tff(c_362,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_348])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_321,c_362])).

tff(c_375,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_547,plain,(
    ! [B_106,A_107] :
      ( r2_hidden(B_106,A_107)
      | ~ m1_subset_1(B_106,A_107)
      | v1_xboole_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_637,plain,(
    ! [B_120,A_121] :
      ( r1_tarski(B_120,A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_121))
      | v1_xboole_0(k1_zfmisc_1(A_121)) ) ),
    inference(resolution,[status(thm)],[c_547,c_8])).

tff(c_647,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_637])).

tff(c_656,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_647])).

tff(c_574,plain,(
    ! [C_110,B_111,A_112] :
      ( r2_hidden(C_110,B_111)
      | ~ r2_hidden(C_110,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_587,plain,(
    ! [C_113,B_114] :
      ( r2_hidden(C_113,B_114)
      | ~ r1_tarski('#skF_6',B_114)
      | ~ m1_subset_1(C_113,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_574])).

tff(c_608,plain,(
    ! [B_114,C_113] :
      ( ~ v1_xboole_0(B_114)
      | ~ r1_tarski('#skF_6',B_114)
      | ~ m1_subset_1(C_113,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_587,c_36])).

tff(c_609,plain,(
    ! [C_113] : ~ m1_subset_1(C_113,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_608])).

tff(c_63,plain,(
    ! [A_15] :
      ( v1_xboole_0('#skF_4'(A_15))
      | ~ v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_34,c_53])).

tff(c_381,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_3'(A_86,B_87),A_86)
      | r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_394,plain,(
    ! [A_86,B_87] :
      ( ~ v1_xboole_0(A_86)
      | r1_tarski(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_381,c_36])).

tff(c_396,plain,(
    ! [B_90,A_91] :
      ( B_90 = A_91
      | ~ r1_tarski(B_90,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_406,plain,(
    ! [B_92,A_93] :
      ( B_92 = A_93
      | ~ r1_tarski(B_92,A_93)
      | ~ v1_xboole_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_394,c_396])).

tff(c_416,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ v1_xboole_0(B_94)
      | ~ v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_394,c_406])).

tff(c_423,plain,(
    ! [A_96] :
      ( A_96 = '#skF_5'
      | ~ v1_xboole_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_375,c_416])).

tff(c_450,plain,(
    ! [A_99] :
      ( '#skF_4'(A_99) = '#skF_5'
      | ~ v1_xboole_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_63,c_423])).

tff(c_457,plain,(
    '#skF_4'('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_375,c_450])).

tff(c_466,plain,(
    m1_subset_1('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_34])).

tff(c_611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_609,c_466])).

tff(c_612,plain,(
    ! [B_114] :
      ( ~ v1_xboole_0(B_114)
      | ~ r1_tarski('#skF_6',B_114) ) ),
    inference(splitRight,[status(thm)],[c_608])).

tff(c_677,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_656,c_612])).

tff(c_686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_677])).

tff(c_689,plain,(
    ! [C_124] : ~ m1_subset_1(C_124,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_694,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_34,c_689])).

%------------------------------------------------------------------------------
