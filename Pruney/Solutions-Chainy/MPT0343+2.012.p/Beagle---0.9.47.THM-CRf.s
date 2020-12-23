%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:18 EST 2020

% Result     : Theorem 6.48s
% Output     : CNFRefutation 6.48s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 494 expanded)
%              Number of leaves         :   22 ( 163 expanded)
%              Depth                    :   12
%              Number of atoms          :  306 (1375 expanded)
%              Number of equality atoms :   13 (  82 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_32,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_xboole_0(A_5,B_6)
      | B_6 = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),B_8)
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_109,plain,(
    ! [D_50] :
      ( r2_hidden(D_50,'#skF_6')
      | ~ r2_hidden(D_50,'#skF_5')
      | ~ m1_subset_1(D_50,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1758,plain,(
    ! [A_167] :
      ( r2_hidden('#skF_2'(A_167,'#skF_5'),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_167,'#skF_5'),'#skF_4')
      | ~ r2_xboole_0(A_167,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_109])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_2'(A_7,B_8),A_7)
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1781,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_6','#skF_5'),'#skF_4')
    | ~ r2_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_1758,c_12])).

tff(c_1790,plain,(
    ~ r2_xboole_0('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1781])).

tff(c_1793,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_1790])).

tff(c_1796,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1793])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    ! [A_16,B_17,C_21] :
      ( m1_subset_1('#skF_3'(A_16,B_17,C_21),A_16)
      | r1_tarski(B_17,C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    ! [A_16,B_17,C_21] :
      ( r2_hidden('#skF_3'(A_16,B_17,C_21),B_17)
      | r1_tarski(B_17,C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    ! [D_27] :
      ( r2_hidden(D_27,'#skF_5')
      | ~ r2_hidden(D_27,'#skF_6')
      | ~ m1_subset_1(D_27,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1036,plain,(
    ! [A_123,B_124,C_125] :
      ( ~ r2_hidden('#skF_3'(A_123,B_124,C_125),C_125)
      | r1_tarski(B_124,C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(A_123))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2552,plain,(
    ! [B_215,A_216] :
      ( r1_tarski(B_215,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_216))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(A_216))
      | ~ r2_hidden('#skF_3'(A_216,B_215,'#skF_5'),'#skF_6')
      | ~ m1_subset_1('#skF_3'(A_216,B_215,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_1036])).

tff(c_2559,plain,(
    ! [A_16] :
      ( ~ m1_subset_1('#skF_3'(A_16,'#skF_6','#skF_5'),'#skF_4')
      | r1_tarski('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_16))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_28,c_2552])).

tff(c_4577,plain,(
    ! [A_310] :
      ( ~ m1_subset_1('#skF_3'(A_310,'#skF_6','#skF_5'),'#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_310))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_310)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1796,c_1796,c_2559])).

tff(c_4581,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_4577])).

tff(c_4587,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_4581])).

tff(c_4589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1796,c_4587])).

tff(c_4591,plain,(
    r2_xboole_0('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1781])).

tff(c_63,plain,(
    ! [D_38] :
      ( r2_hidden(D_38,'#skF_5')
      | ~ r2_hidden(D_38,'#skF_6')
      | ~ m1_subset_1(D_38,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [D_38] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(D_38,'#skF_6')
      | ~ m1_subset_1(D_38,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_154,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_91,plain,(
    ! [B_47,A_48] :
      ( m1_subset_1(B_47,A_48)
      | ~ r2_hidden(B_47,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_101,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1('#skF_2'(A_7,B_8),B_8)
      | v1_xboole_0(B_8)
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_91])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_185,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_123])).

tff(c_186,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_103,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( m1_subset_1(B_11,A_10)
      | ~ v1_xboole_0(B_11)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_190,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_186])).

tff(c_191,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( r2_hidden(B_11,A_10)
      | ~ m1_subset_1(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_155,plain,(
    ! [C_55,A_56,B_57] :
      ( r2_hidden(C_55,A_56)
      | ~ r2_hidden(C_55,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_750,plain,(
    ! [B_105,A_106,A_107] :
      ( r2_hidden(B_105,A_106)
      | ~ m1_subset_1(A_107,k1_zfmisc_1(A_106))
      | ~ m1_subset_1(B_105,A_107)
      | v1_xboole_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_18,c_155])).

tff(c_766,plain,(
    ! [B_105] :
      ( r2_hidden(B_105,'#skF_4')
      | ~ m1_subset_1(B_105,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_750])).

tff(c_805,plain,(
    ! [B_109] :
      ( r2_hidden(B_109,'#skF_4')
      | ~ m1_subset_1(B_109,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_766])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( m1_subset_1(B_11,A_10)
      | ~ r2_hidden(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_818,plain,(
    ! [B_109] :
      ( m1_subset_1(B_109,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_109,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_805,c_16])).

tff(c_886,plain,(
    ! [B_112] :
      ( m1_subset_1(B_112,'#skF_4')
      | ~ m1_subset_1(B_112,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_818])).

tff(c_901,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_886])).

tff(c_915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_186,c_901])).

tff(c_917,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_918,plain,(
    ! [A_113,A_114] :
      ( r2_hidden('#skF_1'(A_113),A_114)
      | ~ m1_subset_1(A_113,k1_zfmisc_1(A_114))
      | v1_xboole_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_4,c_155])).

tff(c_935,plain,(
    ! [A_115,A_116] :
      ( ~ v1_xboole_0(A_115)
      | ~ m1_subset_1(A_116,k1_zfmisc_1(A_115))
      | v1_xboole_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_918,c_2])).

tff(c_949,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_935])).

tff(c_957,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_949])).

tff(c_959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_957])).

tff(c_961,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_22,plain,(
    ! [B_11,A_10] :
      ( v1_xboole_0(B_11)
      | ~ m1_subset_1(B_11,A_10)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_981,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_961,c_22])).

tff(c_1002,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_981])).

tff(c_4743,plain,(
    ! [B_323,A_324,A_325] :
      ( r2_hidden(B_323,A_324)
      | ~ m1_subset_1(A_325,k1_zfmisc_1(A_324))
      | ~ m1_subset_1(B_323,A_325)
      | v1_xboole_0(A_325) ) ),
    inference(resolution,[status(thm)],[c_18,c_155])).

tff(c_4759,plain,(
    ! [B_323] :
      ( r2_hidden(B_323,'#skF_4')
      | ~ m1_subset_1(B_323,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_4743])).

tff(c_4798,plain,(
    ! [B_327] :
      ( r2_hidden(B_327,'#skF_4')
      | ~ m1_subset_1(B_327,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_4759])).

tff(c_4811,plain,(
    ! [B_327] :
      ( m1_subset_1(B_327,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_327,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4798,c_16])).

tff(c_4939,plain,(
    ! [B_330] :
      ( m1_subset_1(B_330,'#skF_4')
      | ~ m1_subset_1(B_330,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1002,c_4811])).

tff(c_4943,plain,(
    ! [A_7] :
      ( m1_subset_1('#skF_2'(A_7,'#skF_5'),'#skF_4')
      | v1_xboole_0('#skF_5')
      | ~ r2_xboole_0(A_7,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_101,c_4939])).

tff(c_5141,plain,(
    ! [A_342] :
      ( m1_subset_1('#skF_2'(A_342,'#skF_5'),'#skF_4')
      | ~ r2_xboole_0(A_342,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_4943])).

tff(c_4590,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1781])).

tff(c_5144,plain,(
    ~ r2_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_5141,c_4590])).

tff(c_5155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4591,c_5144])).

tff(c_5157,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_981])).

tff(c_960,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_24,plain,(
    ! [C_15,A_12,B_13] :
      ( r2_hidden(C_15,A_12)
      | ~ r2_hidden(C_15,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5214,plain,(
    ! [A_349] :
      ( r2_hidden('#skF_1'('#skF_5'),A_349)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_349)) ) ),
    inference(resolution,[status(thm)],[c_960,c_24])).

tff(c_5233,plain,(
    ! [A_350] :
      ( ~ v1_xboole_0(A_350)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_350)) ) ),
    inference(resolution,[status(thm)],[c_5214,c_2])).

tff(c_5239,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_5233])).

tff(c_5244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5157,c_5239])).

tff(c_5246,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_6523,plain,(
    ! [A_490,B_491,C_492] :
      ( r2_hidden('#skF_3'(A_490,B_491,C_492),B_491)
      | r1_tarski(B_491,C_492)
      | ~ m1_subset_1(C_492,k1_zfmisc_1(A_490))
      | ~ m1_subset_1(B_491,k1_zfmisc_1(A_490)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6788,plain,(
    ! [B_517,C_518,A_519] :
      ( ~ v1_xboole_0(B_517)
      | r1_tarski(B_517,C_518)
      | ~ m1_subset_1(C_518,k1_zfmisc_1(A_519))
      | ~ m1_subset_1(B_517,k1_zfmisc_1(A_519)) ) ),
    inference(resolution,[status(thm)],[c_6523,c_2])).

tff(c_6821,plain,(
    ! [B_520] :
      ( ~ v1_xboole_0(B_520)
      | r1_tarski(B_520,'#skF_6')
      | ~ m1_subset_1(B_520,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_34,c_6788])).

tff(c_6847,plain,
    ( ~ v1_xboole_0('#skF_5')
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_6821])).

tff(c_6864,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5246,c_6847])).

tff(c_5260,plain,(
    ! [D_354] :
      ( ~ r2_hidden(D_354,'#skF_6')
      | ~ m1_subset_1(D_354,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_5273,plain,(
    ! [B_11] :
      ( ~ m1_subset_1(B_11,'#skF_4')
      | ~ m1_subset_1(B_11,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_18,c_5260])).

tff(c_5284,plain,(
    ! [B_355] :
      ( ~ m1_subset_1(B_355,'#skF_4')
      | ~ m1_subset_1(B_355,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_5273])).

tff(c_5294,plain,(
    ! [B_11] :
      ( ~ m1_subset_1(B_11,'#skF_4')
      | ~ v1_xboole_0(B_11)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_5284])).

tff(c_5295,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_5294])).

tff(c_5275,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_5260])).

tff(c_5276,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5275])).

tff(c_5280,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_6'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_5276])).

tff(c_5282,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5280])).

tff(c_5247,plain,(
    ! [C_351,A_352,B_353] :
      ( r2_hidden(C_351,A_352)
      | ~ r2_hidden(C_351,B_353)
      | ~ m1_subset_1(B_353,k1_zfmisc_1(A_352)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5573,plain,(
    ! [B_385,A_386,A_387] :
      ( r2_hidden(B_385,A_386)
      | ~ m1_subset_1(A_387,k1_zfmisc_1(A_386))
      | ~ m1_subset_1(B_385,A_387)
      | v1_xboole_0(A_387) ) ),
    inference(resolution,[status(thm)],[c_18,c_5247])).

tff(c_5587,plain,(
    ! [B_385] :
      ( r2_hidden(B_385,'#skF_4')
      | ~ m1_subset_1(B_385,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_5573])).

tff(c_5599,plain,(
    ! [B_388] :
      ( r2_hidden(B_388,'#skF_4')
      | ~ m1_subset_1(B_388,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_5295,c_5587])).

tff(c_5612,plain,(
    ! [B_388] :
      ( m1_subset_1(B_388,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_388,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_5599,c_16])).

tff(c_5623,plain,(
    ! [B_389] :
      ( m1_subset_1(B_389,'#skF_4')
      | ~ m1_subset_1(B_389,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_5282,c_5612])).

tff(c_5635,plain,
    ( m1_subset_1('#skF_1'('#skF_6'),'#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_103,c_5623])).

tff(c_5647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5295,c_5276,c_5635])).

tff(c_5649,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_5294])).

tff(c_5698,plain,(
    ! [A_396,B_397,C_398] :
      ( r2_hidden('#skF_3'(A_396,B_397,C_398),B_397)
      | r1_tarski(B_397,C_398)
      | ~ m1_subset_1(C_398,k1_zfmisc_1(A_396))
      | ~ m1_subset_1(B_397,k1_zfmisc_1(A_396)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6047,plain,(
    ! [B_437,C_438,A_439] :
      ( ~ v1_xboole_0(B_437)
      | r1_tarski(B_437,C_438)
      | ~ m1_subset_1(C_438,k1_zfmisc_1(A_439))
      | ~ m1_subset_1(B_437,k1_zfmisc_1(A_439)) ) ),
    inference(resolution,[status(thm)],[c_5698,c_2])).

tff(c_6074,plain,(
    ! [B_440] :
      ( ~ v1_xboole_0(B_440)
      | r1_tarski(B_440,'#skF_6')
      | ~ m1_subset_1(B_440,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_34,c_6047])).

tff(c_6096,plain,
    ( ~ v1_xboole_0('#skF_5')
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_6074])).

tff(c_6110,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5246,c_6096])).

tff(c_75,plain,(
    ! [A_43,B_44] :
      ( r2_xboole_0(A_43,B_44)
      | B_44 = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_2'(A_39,B_40),B_40)
      | ~ r2_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_73,plain,(
    ! [B_40,A_39] :
      ( ~ v1_xboole_0(B_40)
      | ~ r2_xboole_0(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_69,c_2])).

tff(c_86,plain,(
    ! [B_44,A_43] :
      ( ~ v1_xboole_0(B_44)
      | B_44 = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_75,c_73])).

tff(c_6113,plain,
    ( ~ v1_xboole_0('#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6110,c_86])).

tff(c_6116,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5649,c_6113])).

tff(c_6118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6116])).

tff(c_6120,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5280])).

tff(c_6405,plain,(
    ! [A_475,B_476,A_477] :
      ( r2_hidden('#skF_2'(A_475,B_476),A_477)
      | ~ m1_subset_1(B_476,k1_zfmisc_1(A_477))
      | ~ r2_xboole_0(A_475,B_476) ) ),
    inference(resolution,[status(thm)],[c_14,c_5247])).

tff(c_6483,plain,(
    ! [A_484,B_485,A_486] :
      ( ~ v1_xboole_0(A_484)
      | ~ m1_subset_1(B_485,k1_zfmisc_1(A_484))
      | ~ r2_xboole_0(A_486,B_485) ) ),
    inference(resolution,[status(thm)],[c_6405,c_2])).

tff(c_6497,plain,(
    ! [A_486] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_xboole_0(A_486,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_6483])).

tff(c_6510,plain,(
    ! [A_487] : ~ r2_xboole_0(A_487,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6120,c_6497])).

tff(c_6515,plain,(
    ! [A_5] :
      ( A_5 = '#skF_6'
      | ~ r1_tarski(A_5,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6,c_6510])).

tff(c_6867,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6864,c_6515])).

tff(c_6874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6867])).

tff(c_6875,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_5275])).

tff(c_7065,plain,(
    ! [A_544,B_545,C_546] :
      ( r2_hidden('#skF_3'(A_544,B_545,C_546),B_545)
      | r1_tarski(B_545,C_546)
      | ~ m1_subset_1(C_546,k1_zfmisc_1(A_544))
      | ~ m1_subset_1(B_545,k1_zfmisc_1(A_544)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7256,plain,(
    ! [B_568,C_569,A_570] :
      ( ~ v1_xboole_0(B_568)
      | r1_tarski(B_568,C_569)
      | ~ m1_subset_1(C_569,k1_zfmisc_1(A_570))
      | ~ m1_subset_1(B_568,k1_zfmisc_1(A_570)) ) ),
    inference(resolution,[status(thm)],[c_7065,c_2])).

tff(c_7283,plain,(
    ! [B_571] :
      ( ~ v1_xboole_0(B_571)
      | r1_tarski(B_571,'#skF_6')
      | ~ m1_subset_1(B_571,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_34,c_7256])).

tff(c_7305,plain,
    ( ~ v1_xboole_0('#skF_5')
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_7283])).

tff(c_7319,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5246,c_7305])).

tff(c_7322,plain,
    ( ~ v1_xboole_0('#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7319,c_86])).

tff(c_7325,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6875,c_7322])).

tff(c_7327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_7325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:35:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.48/2.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.48/2.38  
% 6.48/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.48/2.38  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 6.48/2.38  
% 6.48/2.38  %Foreground sorts:
% 6.48/2.38  
% 6.48/2.38  
% 6.48/2.38  %Background operators:
% 6.48/2.38  
% 6.48/2.38  
% 6.48/2.38  %Foreground operators:
% 6.48/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.48/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.48/2.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.48/2.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.48/2.38  tff('#skF_5', type, '#skF_5': $i).
% 6.48/2.38  tff('#skF_6', type, '#skF_6': $i).
% 6.48/2.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.48/2.38  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.48/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.48/2.38  tff('#skF_4', type, '#skF_4': $i).
% 6.48/2.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.48/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.48/2.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.48/2.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.48/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.48/2.38  
% 6.48/2.41  tff(f_97, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 6.48/2.41  tff(f_38, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 6.48/2.41  tff(f_48, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 6.48/2.41  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 6.48/2.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.48/2.41  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.48/2.41  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 6.48/2.41  tff(c_32, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.48/2.41  tff(c_6, plain, (![A_5, B_6]: (r2_xboole_0(A_5, B_6) | B_6=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.48/2.41  tff(c_14, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), B_8) | ~r2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.48/2.41  tff(c_109, plain, (![D_50]: (r2_hidden(D_50, '#skF_6') | ~r2_hidden(D_50, '#skF_5') | ~m1_subset_1(D_50, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.48/2.41  tff(c_1758, plain, (![A_167]: (r2_hidden('#skF_2'(A_167, '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_2'(A_167, '#skF_5'), '#skF_4') | ~r2_xboole_0(A_167, '#skF_5'))), inference(resolution, [status(thm)], [c_14, c_109])).
% 6.48/2.41  tff(c_12, plain, (![A_7, B_8]: (~r2_hidden('#skF_2'(A_7, B_8), A_7) | ~r2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.48/2.41  tff(c_1781, plain, (~m1_subset_1('#skF_2'('#skF_6', '#skF_5'), '#skF_4') | ~r2_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_1758, c_12])).
% 6.48/2.41  tff(c_1790, plain, (~r2_xboole_0('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_1781])).
% 6.48/2.41  tff(c_1793, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_1790])).
% 6.48/2.41  tff(c_1796, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_32, c_1793])).
% 6.48/2.41  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.48/2.41  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.48/2.41  tff(c_30, plain, (![A_16, B_17, C_21]: (m1_subset_1('#skF_3'(A_16, B_17, C_21), A_16) | r1_tarski(B_17, C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.48/2.41  tff(c_28, plain, (![A_16, B_17, C_21]: (r2_hidden('#skF_3'(A_16, B_17, C_21), B_17) | r1_tarski(B_17, C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.48/2.41  tff(c_38, plain, (![D_27]: (r2_hidden(D_27, '#skF_5') | ~r2_hidden(D_27, '#skF_6') | ~m1_subset_1(D_27, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.48/2.41  tff(c_1036, plain, (![A_123, B_124, C_125]: (~r2_hidden('#skF_3'(A_123, B_124, C_125), C_125) | r1_tarski(B_124, C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(A_123)) | ~m1_subset_1(B_124, k1_zfmisc_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.48/2.41  tff(c_2552, plain, (![B_215, A_216]: (r1_tarski(B_215, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_216)) | ~m1_subset_1(B_215, k1_zfmisc_1(A_216)) | ~r2_hidden('#skF_3'(A_216, B_215, '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_3'(A_216, B_215, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_1036])).
% 6.48/2.41  tff(c_2559, plain, (![A_16]: (~m1_subset_1('#skF_3'(A_16, '#skF_6', '#skF_5'), '#skF_4') | r1_tarski('#skF_6', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_16)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_28, c_2552])).
% 6.48/2.41  tff(c_4577, plain, (![A_310]: (~m1_subset_1('#skF_3'(A_310, '#skF_6', '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_310)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_310)))), inference(negUnitSimplification, [status(thm)], [c_1796, c_1796, c_2559])).
% 6.48/2.41  tff(c_4581, plain, (r1_tarski('#skF_6', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_4577])).
% 6.48/2.41  tff(c_4587, plain, (r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_4581])).
% 6.48/2.41  tff(c_4589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1796, c_4587])).
% 6.48/2.41  tff(c_4591, plain, (r2_xboole_0('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_1781])).
% 6.48/2.41  tff(c_63, plain, (![D_38]: (r2_hidden(D_38, '#skF_5') | ~r2_hidden(D_38, '#skF_6') | ~m1_subset_1(D_38, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.48/2.41  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.48/2.41  tff(c_67, plain, (![D_38]: (~v1_xboole_0('#skF_5') | ~r2_hidden(D_38, '#skF_6') | ~m1_subset_1(D_38, '#skF_4'))), inference(resolution, [status(thm)], [c_63, c_2])).
% 6.48/2.41  tff(c_154, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_67])).
% 6.48/2.41  tff(c_91, plain, (![B_47, A_48]: (m1_subset_1(B_47, A_48) | ~r2_hidden(B_47, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.48/2.41  tff(c_101, plain, (![A_7, B_8]: (m1_subset_1('#skF_2'(A_7, B_8), B_8) | v1_xboole_0(B_8) | ~r2_xboole_0(A_7, B_8))), inference(resolution, [status(thm)], [c_14, c_91])).
% 6.48/2.41  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.48/2.41  tff(c_123, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_109])).
% 6.48/2.41  tff(c_185, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_154, c_123])).
% 6.48/2.41  tff(c_186, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_185])).
% 6.48/2.41  tff(c_103, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_91])).
% 6.48/2.41  tff(c_20, plain, (![B_11, A_10]: (m1_subset_1(B_11, A_10) | ~v1_xboole_0(B_11) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.48/2.41  tff(c_190, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_20, c_186])).
% 6.48/2.41  tff(c_191, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_190])).
% 6.48/2.41  tff(c_18, plain, (![B_11, A_10]: (r2_hidden(B_11, A_10) | ~m1_subset_1(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.48/2.41  tff(c_155, plain, (![C_55, A_56, B_57]: (r2_hidden(C_55, A_56) | ~r2_hidden(C_55, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.48/2.41  tff(c_750, plain, (![B_105, A_106, A_107]: (r2_hidden(B_105, A_106) | ~m1_subset_1(A_107, k1_zfmisc_1(A_106)) | ~m1_subset_1(B_105, A_107) | v1_xboole_0(A_107))), inference(resolution, [status(thm)], [c_18, c_155])).
% 6.48/2.41  tff(c_766, plain, (![B_105]: (r2_hidden(B_105, '#skF_4') | ~m1_subset_1(B_105, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_750])).
% 6.48/2.41  tff(c_805, plain, (![B_109]: (r2_hidden(B_109, '#skF_4') | ~m1_subset_1(B_109, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_154, c_766])).
% 6.48/2.41  tff(c_16, plain, (![B_11, A_10]: (m1_subset_1(B_11, A_10) | ~r2_hidden(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.48/2.41  tff(c_818, plain, (![B_109]: (m1_subset_1(B_109, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_109, '#skF_5'))), inference(resolution, [status(thm)], [c_805, c_16])).
% 6.48/2.41  tff(c_886, plain, (![B_112]: (m1_subset_1(B_112, '#skF_4') | ~m1_subset_1(B_112, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_191, c_818])).
% 6.48/2.41  tff(c_901, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_103, c_886])).
% 6.48/2.41  tff(c_915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_186, c_901])).
% 6.48/2.41  tff(c_917, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_190])).
% 6.48/2.41  tff(c_918, plain, (![A_113, A_114]: (r2_hidden('#skF_1'(A_113), A_114) | ~m1_subset_1(A_113, k1_zfmisc_1(A_114)) | v1_xboole_0(A_113))), inference(resolution, [status(thm)], [c_4, c_155])).
% 6.48/2.41  tff(c_935, plain, (![A_115, A_116]: (~v1_xboole_0(A_115) | ~m1_subset_1(A_116, k1_zfmisc_1(A_115)) | v1_xboole_0(A_116))), inference(resolution, [status(thm)], [c_918, c_2])).
% 6.48/2.41  tff(c_949, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_935])).
% 6.48/2.41  tff(c_957, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_917, c_949])).
% 6.48/2.41  tff(c_959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_957])).
% 6.48/2.41  tff(c_961, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_185])).
% 6.48/2.41  tff(c_22, plain, (![B_11, A_10]: (v1_xboole_0(B_11) | ~m1_subset_1(B_11, A_10) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.48/2.41  tff(c_981, plain, (v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_961, c_22])).
% 6.48/2.41  tff(c_1002, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_981])).
% 6.48/2.41  tff(c_4743, plain, (![B_323, A_324, A_325]: (r2_hidden(B_323, A_324) | ~m1_subset_1(A_325, k1_zfmisc_1(A_324)) | ~m1_subset_1(B_323, A_325) | v1_xboole_0(A_325))), inference(resolution, [status(thm)], [c_18, c_155])).
% 6.48/2.41  tff(c_4759, plain, (![B_323]: (r2_hidden(B_323, '#skF_4') | ~m1_subset_1(B_323, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_4743])).
% 6.48/2.41  tff(c_4798, plain, (![B_327]: (r2_hidden(B_327, '#skF_4') | ~m1_subset_1(B_327, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_154, c_4759])).
% 6.48/2.41  tff(c_4811, plain, (![B_327]: (m1_subset_1(B_327, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_327, '#skF_5'))), inference(resolution, [status(thm)], [c_4798, c_16])).
% 6.48/2.41  tff(c_4939, plain, (![B_330]: (m1_subset_1(B_330, '#skF_4') | ~m1_subset_1(B_330, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1002, c_4811])).
% 6.48/2.41  tff(c_4943, plain, (![A_7]: (m1_subset_1('#skF_2'(A_7, '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | ~r2_xboole_0(A_7, '#skF_5'))), inference(resolution, [status(thm)], [c_101, c_4939])).
% 6.48/2.41  tff(c_5141, plain, (![A_342]: (m1_subset_1('#skF_2'(A_342, '#skF_5'), '#skF_4') | ~r2_xboole_0(A_342, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_154, c_4943])).
% 6.48/2.41  tff(c_4590, plain, (~m1_subset_1('#skF_2'('#skF_6', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_1781])).
% 6.48/2.41  tff(c_5144, plain, (~r2_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_5141, c_4590])).
% 6.48/2.41  tff(c_5155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4591, c_5144])).
% 6.48/2.41  tff(c_5157, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_981])).
% 6.48/2.41  tff(c_960, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_185])).
% 6.48/2.41  tff(c_24, plain, (![C_15, A_12, B_13]: (r2_hidden(C_15, A_12) | ~r2_hidden(C_15, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.48/2.41  tff(c_5214, plain, (![A_349]: (r2_hidden('#skF_1'('#skF_5'), A_349) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_349)))), inference(resolution, [status(thm)], [c_960, c_24])).
% 6.48/2.41  tff(c_5233, plain, (![A_350]: (~v1_xboole_0(A_350) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_350)))), inference(resolution, [status(thm)], [c_5214, c_2])).
% 6.48/2.41  tff(c_5239, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_5233])).
% 6.48/2.41  tff(c_5244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5157, c_5239])).
% 6.48/2.41  tff(c_5246, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_67])).
% 6.48/2.41  tff(c_6523, plain, (![A_490, B_491, C_492]: (r2_hidden('#skF_3'(A_490, B_491, C_492), B_491) | r1_tarski(B_491, C_492) | ~m1_subset_1(C_492, k1_zfmisc_1(A_490)) | ~m1_subset_1(B_491, k1_zfmisc_1(A_490)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.48/2.41  tff(c_6788, plain, (![B_517, C_518, A_519]: (~v1_xboole_0(B_517) | r1_tarski(B_517, C_518) | ~m1_subset_1(C_518, k1_zfmisc_1(A_519)) | ~m1_subset_1(B_517, k1_zfmisc_1(A_519)))), inference(resolution, [status(thm)], [c_6523, c_2])).
% 6.48/2.41  tff(c_6821, plain, (![B_520]: (~v1_xboole_0(B_520) | r1_tarski(B_520, '#skF_6') | ~m1_subset_1(B_520, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_34, c_6788])).
% 6.48/2.41  tff(c_6847, plain, (~v1_xboole_0('#skF_5') | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_36, c_6821])).
% 6.48/2.41  tff(c_6864, plain, (r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5246, c_6847])).
% 6.48/2.41  tff(c_5260, plain, (![D_354]: (~r2_hidden(D_354, '#skF_6') | ~m1_subset_1(D_354, '#skF_4'))), inference(splitRight, [status(thm)], [c_67])).
% 6.48/2.41  tff(c_5273, plain, (![B_11]: (~m1_subset_1(B_11, '#skF_4') | ~m1_subset_1(B_11, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_18, c_5260])).
% 6.48/2.41  tff(c_5284, plain, (![B_355]: (~m1_subset_1(B_355, '#skF_4') | ~m1_subset_1(B_355, '#skF_6'))), inference(splitLeft, [status(thm)], [c_5273])).
% 6.48/2.41  tff(c_5294, plain, (![B_11]: (~m1_subset_1(B_11, '#skF_4') | ~v1_xboole_0(B_11) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_5284])).
% 6.48/2.41  tff(c_5295, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_5294])).
% 6.48/2.41  tff(c_5275, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_4') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_5260])).
% 6.48/2.41  tff(c_5276, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_5275])).
% 6.48/2.41  tff(c_5280, plain, (~v1_xboole_0('#skF_1'('#skF_6')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_20, c_5276])).
% 6.48/2.41  tff(c_5282, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_5280])).
% 6.48/2.41  tff(c_5247, plain, (![C_351, A_352, B_353]: (r2_hidden(C_351, A_352) | ~r2_hidden(C_351, B_353) | ~m1_subset_1(B_353, k1_zfmisc_1(A_352)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.48/2.41  tff(c_5573, plain, (![B_385, A_386, A_387]: (r2_hidden(B_385, A_386) | ~m1_subset_1(A_387, k1_zfmisc_1(A_386)) | ~m1_subset_1(B_385, A_387) | v1_xboole_0(A_387))), inference(resolution, [status(thm)], [c_18, c_5247])).
% 6.48/2.41  tff(c_5587, plain, (![B_385]: (r2_hidden(B_385, '#skF_4') | ~m1_subset_1(B_385, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_5573])).
% 6.48/2.41  tff(c_5599, plain, (![B_388]: (r2_hidden(B_388, '#skF_4') | ~m1_subset_1(B_388, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_5295, c_5587])).
% 6.48/2.41  tff(c_5612, plain, (![B_388]: (m1_subset_1(B_388, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_388, '#skF_6'))), inference(resolution, [status(thm)], [c_5599, c_16])).
% 6.48/2.41  tff(c_5623, plain, (![B_389]: (m1_subset_1(B_389, '#skF_4') | ~m1_subset_1(B_389, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_5282, c_5612])).
% 6.48/2.41  tff(c_5635, plain, (m1_subset_1('#skF_1'('#skF_6'), '#skF_4') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_103, c_5623])).
% 6.48/2.41  tff(c_5647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5295, c_5276, c_5635])).
% 6.48/2.41  tff(c_5649, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_5294])).
% 6.48/2.41  tff(c_5698, plain, (![A_396, B_397, C_398]: (r2_hidden('#skF_3'(A_396, B_397, C_398), B_397) | r1_tarski(B_397, C_398) | ~m1_subset_1(C_398, k1_zfmisc_1(A_396)) | ~m1_subset_1(B_397, k1_zfmisc_1(A_396)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.48/2.41  tff(c_6047, plain, (![B_437, C_438, A_439]: (~v1_xboole_0(B_437) | r1_tarski(B_437, C_438) | ~m1_subset_1(C_438, k1_zfmisc_1(A_439)) | ~m1_subset_1(B_437, k1_zfmisc_1(A_439)))), inference(resolution, [status(thm)], [c_5698, c_2])).
% 6.48/2.41  tff(c_6074, plain, (![B_440]: (~v1_xboole_0(B_440) | r1_tarski(B_440, '#skF_6') | ~m1_subset_1(B_440, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_34, c_6047])).
% 6.48/2.41  tff(c_6096, plain, (~v1_xboole_0('#skF_5') | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_36, c_6074])).
% 6.48/2.41  tff(c_6110, plain, (r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5246, c_6096])).
% 6.48/2.41  tff(c_75, plain, (![A_43, B_44]: (r2_xboole_0(A_43, B_44) | B_44=A_43 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.48/2.41  tff(c_69, plain, (![A_39, B_40]: (r2_hidden('#skF_2'(A_39, B_40), B_40) | ~r2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.48/2.41  tff(c_73, plain, (![B_40, A_39]: (~v1_xboole_0(B_40) | ~r2_xboole_0(A_39, B_40))), inference(resolution, [status(thm)], [c_69, c_2])).
% 6.48/2.41  tff(c_86, plain, (![B_44, A_43]: (~v1_xboole_0(B_44) | B_44=A_43 | ~r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_75, c_73])).
% 6.48/2.41  tff(c_6113, plain, (~v1_xboole_0('#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_6110, c_86])).
% 6.48/2.41  tff(c_6116, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5649, c_6113])).
% 6.48/2.41  tff(c_6118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_6116])).
% 6.48/2.41  tff(c_6120, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_5280])).
% 6.48/2.41  tff(c_6405, plain, (![A_475, B_476, A_477]: (r2_hidden('#skF_2'(A_475, B_476), A_477) | ~m1_subset_1(B_476, k1_zfmisc_1(A_477)) | ~r2_xboole_0(A_475, B_476))), inference(resolution, [status(thm)], [c_14, c_5247])).
% 6.48/2.41  tff(c_6483, plain, (![A_484, B_485, A_486]: (~v1_xboole_0(A_484) | ~m1_subset_1(B_485, k1_zfmisc_1(A_484)) | ~r2_xboole_0(A_486, B_485))), inference(resolution, [status(thm)], [c_6405, c_2])).
% 6.48/2.41  tff(c_6497, plain, (![A_486]: (~v1_xboole_0('#skF_4') | ~r2_xboole_0(A_486, '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_6483])).
% 6.48/2.41  tff(c_6510, plain, (![A_487]: (~r2_xboole_0(A_487, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6120, c_6497])).
% 6.48/2.41  tff(c_6515, plain, (![A_5]: (A_5='#skF_6' | ~r1_tarski(A_5, '#skF_6'))), inference(resolution, [status(thm)], [c_6, c_6510])).
% 6.48/2.41  tff(c_6867, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_6864, c_6515])).
% 6.48/2.41  tff(c_6874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_6867])).
% 6.48/2.41  tff(c_6875, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_5275])).
% 6.48/2.41  tff(c_7065, plain, (![A_544, B_545, C_546]: (r2_hidden('#skF_3'(A_544, B_545, C_546), B_545) | r1_tarski(B_545, C_546) | ~m1_subset_1(C_546, k1_zfmisc_1(A_544)) | ~m1_subset_1(B_545, k1_zfmisc_1(A_544)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.48/2.41  tff(c_7256, plain, (![B_568, C_569, A_570]: (~v1_xboole_0(B_568) | r1_tarski(B_568, C_569) | ~m1_subset_1(C_569, k1_zfmisc_1(A_570)) | ~m1_subset_1(B_568, k1_zfmisc_1(A_570)))), inference(resolution, [status(thm)], [c_7065, c_2])).
% 6.48/2.41  tff(c_7283, plain, (![B_571]: (~v1_xboole_0(B_571) | r1_tarski(B_571, '#skF_6') | ~m1_subset_1(B_571, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_34, c_7256])).
% 6.48/2.41  tff(c_7305, plain, (~v1_xboole_0('#skF_5') | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_36, c_7283])).
% 6.48/2.41  tff(c_7319, plain, (r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5246, c_7305])).
% 6.48/2.41  tff(c_7322, plain, (~v1_xboole_0('#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_7319, c_86])).
% 6.48/2.41  tff(c_7325, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6875, c_7322])).
% 6.48/2.41  tff(c_7327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_7325])).
% 6.48/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.48/2.41  
% 6.48/2.41  Inference rules
% 6.48/2.41  ----------------------
% 6.48/2.41  #Ref     : 0
% 6.48/2.41  #Sup     : 1375
% 6.48/2.41  #Fact    : 0
% 6.48/2.41  #Define  : 0
% 6.48/2.41  #Split   : 57
% 6.48/2.41  #Chain   : 0
% 6.48/2.41  #Close   : 0
% 6.48/2.41  
% 6.48/2.41  Ordering : KBO
% 6.48/2.41  
% 6.48/2.41  Simplification rules
% 6.48/2.41  ----------------------
% 6.48/2.41  #Subsume      : 401
% 6.48/2.41  #Demod        : 181
% 6.48/2.41  #Tautology    : 140
% 6.48/2.41  #SimpNegUnit  : 416
% 6.48/2.41  #BackRed      : 14
% 6.48/2.41  
% 6.48/2.41  #Partial instantiations: 0
% 6.48/2.41  #Strategies tried      : 1
% 6.48/2.41  
% 6.48/2.41  Timing (in seconds)
% 6.48/2.41  ----------------------
% 6.48/2.41  Preprocessing        : 0.32
% 6.48/2.41  Parsing              : 0.17
% 6.48/2.41  CNF conversion       : 0.02
% 6.48/2.41  Main loop            : 1.26
% 6.48/2.41  Inferencing          : 0.45
% 6.48/2.41  Reduction            : 0.32
% 6.48/2.41  Demodulation         : 0.18
% 6.48/2.41  BG Simplification    : 0.04
% 6.48/2.41  Subsumption          : 0.33
% 6.48/2.41  Abstraction          : 0.05
% 6.48/2.41  MUC search           : 0.00
% 6.48/2.41  Cooper               : 0.00
% 6.48/2.41  Total                : 1.63
% 6.48/2.42  Index Insertion      : 0.00
% 6.48/2.42  Index Deletion       : 0.00
% 6.48/2.42  Index Matching       : 0.00
% 6.48/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
