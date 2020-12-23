%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:17 EST 2020

% Result     : Theorem 5.86s
% Output     : CNFRefutation 5.95s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 846 expanded)
%              Number of leaves         :   22 ( 279 expanded)
%              Depth                    :   16
%              Number of atoms          :  284 (2151 expanded)
%              Number of equality atoms :   21 ( 178 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_50,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_32,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( m1_subset_1(B_16,A_15)
      | ~ v1_xboole_0(B_16)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_206,plain,(
    ! [B_57,A_58] :
      ( r2_hidden(B_57,A_58)
      | ~ m1_subset_1(B_57,A_58)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_14] : k3_tarski(k1_zfmisc_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_59,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,k3_tarski(B_30))
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_62,plain,(
    ! [A_29,A_14] :
      ( r1_tarski(A_29,A_14)
      | ~ r2_hidden(A_29,k1_zfmisc_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_59])).

tff(c_221,plain,(
    ! [B_57,A_14] :
      ( r1_tarski(B_57,A_14)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_14))
      | v1_xboole_0(k1_zfmisc_1(A_14)) ) ),
    inference(resolution,[status(thm)],[c_206,c_62])).

tff(c_247,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(B_60,A_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_221])).

tff(c_271,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_247])).

tff(c_100,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_2'(A_41,B_42),A_41)
      | r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [A_41,B_42] :
      ( ~ v1_xboole_0(A_41)
      | r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_147,plain,(
    ! [B_49,A_50] :
      ( B_49 = A_50
      | ~ r1_tarski(B_49,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_156,plain,(
    ! [B_42,A_41] :
      ( B_42 = A_41
      | ~ r1_tarski(B_42,A_41)
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_113,c_147])).

tff(c_278,plain,
    ( '#skF_5' = '#skF_3'
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_271,c_156])).

tff(c_287,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [B_39,A_40] :
      ( m1_subset_1(B_39,A_40)
      | ~ r2_hidden(B_39,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_99,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r2_hidden(B_16,A_15)
      | ~ m1_subset_1(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_63,plain,(
    ! [D_31] :
      ( r2_hidden(D_31,'#skF_5')
      | ~ r2_hidden(D_31,'#skF_4')
      | ~ m1_subset_1(D_31,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_67,plain,(
    ! [D_31] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(D_31,'#skF_4')
      | ~ m1_subset_1(D_31,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_314,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_132,plain,(
    ! [D_48] :
      ( r2_hidden(D_48,'#skF_4')
      | ~ r2_hidden(D_48,'#skF_5')
      | ~ m1_subset_1(D_48,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_146,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_132])).

tff(c_315,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_293,plain,(
    ! [C_62,B_63,A_64] :
      ( r2_hidden(C_62,B_63)
      | ~ r2_hidden(C_62,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1676,plain,(
    ! [B_163,B_164,A_165] :
      ( r2_hidden(B_163,B_164)
      | ~ r1_tarski(A_165,B_164)
      | ~ m1_subset_1(B_163,A_165)
      | v1_xboole_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_24,c_293])).

tff(c_1680,plain,(
    ! [B_163] :
      ( r2_hidden(B_163,'#skF_3')
      | ~ m1_subset_1(B_163,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_271,c_1676])).

tff(c_1718,plain,(
    ! [B_167] :
      ( r2_hidden(B_167,'#skF_3')
      | ~ m1_subset_1(B_167,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_1680])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( m1_subset_1(B_16,A_15)
      | ~ r2_hidden(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1727,plain,(
    ! [B_167] :
      ( m1_subset_1(B_167,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_167,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1718,c_22])).

tff(c_1789,plain,(
    ! [B_170] :
      ( m1_subset_1(B_170,'#skF_3')
      | ~ m1_subset_1(B_170,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_1727])).

tff(c_1803,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_99,c_1789])).

tff(c_1817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_315,c_1803])).

tff(c_1818,plain,
    ( v1_xboole_0('#skF_5')
    | r2_hidden('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_1824,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_1818])).

tff(c_1835,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1824,c_2])).

tff(c_111,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1('#skF_2'(A_41,B_42),A_41)
      | v1_xboole_0(A_41)
      | r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_100,c_22])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_272,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_247])).

tff(c_3478,plain,(
    ! [B_273,B_274,A_275] :
      ( r2_hidden(B_273,B_274)
      | ~ r1_tarski(A_275,B_274)
      | ~ m1_subset_1(B_273,A_275)
      | v1_xboole_0(A_275) ) ),
    inference(resolution,[status(thm)],[c_24,c_293])).

tff(c_3490,plain,(
    ! [B_273] :
      ( r2_hidden(B_273,'#skF_3')
      | ~ m1_subset_1(B_273,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_272,c_3478])).

tff(c_3538,plain,(
    ! [B_277] :
      ( r2_hidden(B_277,'#skF_3')
      | ~ m1_subset_1(B_277,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1835,c_3490])).

tff(c_3549,plain,(
    ! [B_277] :
      ( m1_subset_1(B_277,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_277,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3538,c_22])).

tff(c_3591,plain,(
    ! [B_279] :
      ( m1_subset_1(B_279,'#skF_3')
      | ~ m1_subset_1(B_279,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_3549])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,(
    ! [D_22] :
      ( r2_hidden(D_22,'#skF_5')
      | ~ r2_hidden(D_22,'#skF_4')
      | ~ m1_subset_1(D_22,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_120,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden('#skF_2'(A_46,B_47),B_47)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3143,plain,(
    ! [A_255] :
      ( r1_tarski(A_255,'#skF_5')
      | ~ r2_hidden('#skF_2'(A_255,'#skF_5'),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_255,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_120])).

tff(c_3158,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_3143])).

tff(c_3201,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3158])).

tff(c_3606,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3591,c_3201])).

tff(c_3617,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_111,c_3606])).

tff(c_3623,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1835,c_3617])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3639,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_3623,c_12])).

tff(c_3651,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3639])).

tff(c_3492,plain,(
    ! [B_273] :
      ( r2_hidden(B_273,'#skF_3')
      | ~ m1_subset_1(B_273,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_271,c_3478])).

tff(c_3516,plain,(
    ! [B_276] :
      ( r2_hidden(B_276,'#skF_3')
      | ~ m1_subset_1(B_276,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_3492])).

tff(c_3527,plain,(
    ! [B_276] :
      ( m1_subset_1(B_276,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_276,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3516,c_22])).

tff(c_3560,plain,(
    ! [B_278] :
      ( m1_subset_1(B_278,'#skF_3')
      | ~ m1_subset_1(B_278,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_3527])).

tff(c_3564,plain,(
    ! [B_42] :
      ( m1_subset_1('#skF_2'('#skF_5',B_42),'#skF_3')
      | v1_xboole_0('#skF_5')
      | r1_tarski('#skF_5',B_42) ) ),
    inference(resolution,[status(thm)],[c_111,c_3560])).

tff(c_3806,plain,(
    ! [B_288] :
      ( m1_subset_1('#skF_2'('#skF_5',B_288),'#skF_3')
      | r1_tarski('#skF_5',B_288) ) ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_3564])).

tff(c_3322,plain,(
    ! [B_267] :
      ( r2_hidden('#skF_2'('#skF_5',B_267),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_267),'#skF_3')
      | r1_tarski('#skF_5',B_267) ) ),
    inference(resolution,[status(thm)],[c_10,c_132])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3349,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_3')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_3322,c_8])).

tff(c_3354,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3349])).

tff(c_3809,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_3806,c_3354])).

tff(c_3820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3651,c_3809])).

tff(c_3821,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_3349])).

tff(c_3835,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_3821,c_12])).

tff(c_3844,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3835])).

tff(c_3944,plain,(
    ! [B_293,B_294,A_295] :
      ( r2_hidden(B_293,B_294)
      | ~ r1_tarski(A_295,B_294)
      | ~ m1_subset_1(B_293,A_295)
      | v1_xboole_0(A_295) ) ),
    inference(resolution,[status(thm)],[c_24,c_293])).

tff(c_3958,plain,(
    ! [B_293] :
      ( r2_hidden(B_293,'#skF_3')
      | ~ m1_subset_1(B_293,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_272,c_3944])).

tff(c_4042,plain,(
    ! [B_298] :
      ( r2_hidden(B_298,'#skF_3')
      | ~ m1_subset_1(B_298,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1835,c_3958])).

tff(c_4053,plain,(
    ! [B_298] :
      ( m1_subset_1(B_298,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_298,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4042,c_22])).

tff(c_4125,plain,(
    ! [B_301] :
      ( m1_subset_1(B_301,'#skF_3')
      | ~ m1_subset_1(B_301,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_4053])).

tff(c_4136,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4125,c_3201])).

tff(c_4143,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_111,c_4136])).

tff(c_4150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3844,c_1835,c_4143])).

tff(c_4151,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_3158])).

tff(c_4191,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_4151,c_12])).

tff(c_4202,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_4191])).

tff(c_4153,plain,(
    ! [B_302,B_303,A_304] :
      ( r2_hidden(B_302,B_303)
      | ~ r1_tarski(A_304,B_303)
      | ~ m1_subset_1(B_302,A_304)
      | v1_xboole_0(A_304) ) ),
    inference(resolution,[status(thm)],[c_24,c_293])).

tff(c_4159,plain,(
    ! [B_302] :
      ( r2_hidden(B_302,'#skF_3')
      | ~ m1_subset_1(B_302,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_271,c_4153])).

tff(c_4272,plain,(
    ! [B_307] :
      ( r2_hidden(B_307,'#skF_3')
      | ~ m1_subset_1(B_307,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_4159])).

tff(c_4281,plain,(
    ! [B_307] :
      ( m1_subset_1(B_307,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_307,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4272,c_22])).

tff(c_4392,plain,(
    ! [B_314] :
      ( m1_subset_1(B_314,'#skF_3')
      | ~ m1_subset_1(B_314,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_4281])).

tff(c_4399,plain,(
    ! [B_42] :
      ( m1_subset_1('#skF_2'('#skF_5',B_42),'#skF_3')
      | v1_xboole_0('#skF_5')
      | r1_tarski('#skF_5',B_42) ) ),
    inference(resolution,[status(thm)],[c_111,c_4392])).

tff(c_4678,plain,(
    ! [B_330] :
      ( m1_subset_1('#skF_2'('#skF_5',B_330),'#skF_3')
      | r1_tarski('#skF_5',B_330) ) ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_4399])).

tff(c_4211,plain,(
    ! [B_305] :
      ( r2_hidden('#skF_2'('#skF_5',B_305),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_305),'#skF_3')
      | r1_tarski('#skF_5',B_305) ) ),
    inference(resolution,[status(thm)],[c_10,c_132])).

tff(c_4226,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_3')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_4211,c_8])).

tff(c_4240,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_4202,c_4202,c_4226])).

tff(c_4681,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_4678,c_4240])).

tff(c_4692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4202,c_4681])).

tff(c_4704,plain,(
    ! [D_332] :
      ( ~ r2_hidden(D_332,'#skF_4')
      | ~ m1_subset_1(D_332,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_4717,plain,(
    ! [B_16] :
      ( ~ m1_subset_1(B_16,'#skF_3')
      | ~ m1_subset_1(B_16,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_4704])).

tff(c_4727,plain,(
    ! [B_333] :
      ( ~ m1_subset_1(B_333,'#skF_3')
      | ~ m1_subset_1(B_333,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_4717])).

tff(c_4731,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_99,c_4727])).

tff(c_4738,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_4731])).

tff(c_4743,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_3'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_4738])).

tff(c_4744,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4743])).

tff(c_5330,plain,(
    ! [B_382,B_383,A_384] :
      ( r2_hidden(B_382,B_383)
      | ~ r1_tarski(A_384,B_383)
      | ~ m1_subset_1(B_382,A_384)
      | v1_xboole_0(A_384) ) ),
    inference(resolution,[status(thm)],[c_24,c_293])).

tff(c_5338,plain,(
    ! [B_382] :
      ( r2_hidden(B_382,'#skF_3')
      | ~ m1_subset_1(B_382,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_272,c_5330])).

tff(c_5362,plain,(
    ! [B_385] :
      ( r2_hidden(B_385,'#skF_3')
      | ~ m1_subset_1(B_385,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_4744,c_5338])).

tff(c_5371,plain,(
    ! [B_385] :
      ( m1_subset_1(B_385,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_385,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5362,c_22])).

tff(c_5381,plain,(
    ! [B_386] :
      ( m1_subset_1(B_386,'#skF_3')
      | ~ m1_subset_1(B_386,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_5371])).

tff(c_4725,plain,(
    ! [B_16] :
      ( ~ m1_subset_1(B_16,'#skF_3')
      | ~ m1_subset_1(B_16,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_4717])).

tff(c_5421,plain,(
    ! [B_387] : ~ m1_subset_1(B_387,'#skF_4') ),
    inference(resolution,[status(thm)],[c_5381,c_4725])).

tff(c_5429,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_99,c_5421])).

tff(c_5440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4744,c_5429])).

tff(c_5442,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4743])).

tff(c_4694,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_163,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_113,c_147])).

tff(c_176,plain,(
    ! [B_42,A_41] :
      ( B_42 = A_41
      | ~ v1_xboole_0(B_42)
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_113,c_163])).

tff(c_4697,plain,(
    ! [A_41] :
      ( A_41 = '#skF_5'
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_4694,c_176])).

tff(c_5446,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5442,c_4697])).

tff(c_5452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_5446])).

tff(c_5453,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4717])).

tff(c_5456,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5453,c_4697])).

tff(c_5462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_5456])).

tff(c_5463,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_5469,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5463,c_32])).

tff(c_5464,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_285,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_272,c_156])).

tff(c_5492,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5464,c_285])).

tff(c_5493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5469,c_5492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:09:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.86/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.95/2.07  
% 5.95/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.95/2.08  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 5.95/2.08  
% 5.95/2.08  %Foreground sorts:
% 5.95/2.08  
% 5.95/2.08  
% 5.95/2.08  %Background operators:
% 5.95/2.08  
% 5.95/2.08  
% 5.95/2.08  %Foreground operators:
% 5.95/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.95/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.95/2.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.95/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.95/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.95/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.95/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.95/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.95/2.08  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.95/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.95/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.95/2.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.95/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.95/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.95/2.08  
% 5.95/2.10  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 5.95/2.10  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 5.95/2.10  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.95/2.10  tff(f_50, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 5.95/2.10  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 5.95/2.10  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.95/2.10  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.95/2.10  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.95/2.10  tff(c_32, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.95/2.10  tff(c_26, plain, (![B_16, A_15]: (m1_subset_1(B_16, A_15) | ~v1_xboole_0(B_16) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.95/2.10  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.95/2.10  tff(c_30, plain, (![A_17]: (~v1_xboole_0(k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.95/2.10  tff(c_206, plain, (![B_57, A_58]: (r2_hidden(B_57, A_58) | ~m1_subset_1(B_57, A_58) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.95/2.10  tff(c_20, plain, (![A_14]: (k3_tarski(k1_zfmisc_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.95/2.10  tff(c_59, plain, (![A_29, B_30]: (r1_tarski(A_29, k3_tarski(B_30)) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.95/2.10  tff(c_62, plain, (![A_29, A_14]: (r1_tarski(A_29, A_14) | ~r2_hidden(A_29, k1_zfmisc_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_59])).
% 5.95/2.10  tff(c_221, plain, (![B_57, A_14]: (r1_tarski(B_57, A_14) | ~m1_subset_1(B_57, k1_zfmisc_1(A_14)) | v1_xboole_0(k1_zfmisc_1(A_14)))), inference(resolution, [status(thm)], [c_206, c_62])).
% 5.95/2.10  tff(c_247, plain, (![B_60, A_61]: (r1_tarski(B_60, A_61) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)))), inference(negUnitSimplification, [status(thm)], [c_30, c_221])).
% 5.95/2.10  tff(c_271, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_247])).
% 5.95/2.10  tff(c_100, plain, (![A_41, B_42]: (r2_hidden('#skF_2'(A_41, B_42), A_41) | r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.95/2.10  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.95/2.10  tff(c_113, plain, (![A_41, B_42]: (~v1_xboole_0(A_41) | r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_100, c_2])).
% 5.95/2.10  tff(c_147, plain, (![B_49, A_50]: (B_49=A_50 | ~r1_tarski(B_49, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.95/2.10  tff(c_156, plain, (![B_42, A_41]: (B_42=A_41 | ~r1_tarski(B_42, A_41) | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_113, c_147])).
% 5.95/2.10  tff(c_278, plain, ('#skF_5'='#skF_3' | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_271, c_156])).
% 5.95/2.10  tff(c_287, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_278])).
% 5.95/2.10  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.95/2.10  tff(c_91, plain, (![B_39, A_40]: (m1_subset_1(B_39, A_40) | ~r2_hidden(B_39, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.95/2.10  tff(c_99, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_91])).
% 5.95/2.10  tff(c_24, plain, (![B_16, A_15]: (r2_hidden(B_16, A_15) | ~m1_subset_1(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.95/2.10  tff(c_63, plain, (![D_31]: (r2_hidden(D_31, '#skF_5') | ~r2_hidden(D_31, '#skF_4') | ~m1_subset_1(D_31, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.95/2.10  tff(c_67, plain, (![D_31]: (~v1_xboole_0('#skF_5') | ~r2_hidden(D_31, '#skF_4') | ~m1_subset_1(D_31, '#skF_3'))), inference(resolution, [status(thm)], [c_63, c_2])).
% 5.95/2.10  tff(c_314, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_67])).
% 5.95/2.10  tff(c_132, plain, (![D_48]: (r2_hidden(D_48, '#skF_4') | ~r2_hidden(D_48, '#skF_5') | ~m1_subset_1(D_48, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.95/2.10  tff(c_146, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_132])).
% 5.95/2.10  tff(c_315, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_146])).
% 5.95/2.10  tff(c_293, plain, (![C_62, B_63, A_64]: (r2_hidden(C_62, B_63) | ~r2_hidden(C_62, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.95/2.10  tff(c_1676, plain, (![B_163, B_164, A_165]: (r2_hidden(B_163, B_164) | ~r1_tarski(A_165, B_164) | ~m1_subset_1(B_163, A_165) | v1_xboole_0(A_165))), inference(resolution, [status(thm)], [c_24, c_293])).
% 5.95/2.10  tff(c_1680, plain, (![B_163]: (r2_hidden(B_163, '#skF_3') | ~m1_subset_1(B_163, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_271, c_1676])).
% 5.95/2.10  tff(c_1718, plain, (![B_167]: (r2_hidden(B_167, '#skF_3') | ~m1_subset_1(B_167, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_314, c_1680])).
% 5.95/2.10  tff(c_22, plain, (![B_16, A_15]: (m1_subset_1(B_16, A_15) | ~r2_hidden(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.95/2.10  tff(c_1727, plain, (![B_167]: (m1_subset_1(B_167, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_167, '#skF_5'))), inference(resolution, [status(thm)], [c_1718, c_22])).
% 5.95/2.10  tff(c_1789, plain, (![B_170]: (m1_subset_1(B_170, '#skF_3') | ~m1_subset_1(B_170, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_287, c_1727])).
% 5.95/2.10  tff(c_1803, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_99, c_1789])).
% 5.95/2.10  tff(c_1817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_314, c_315, c_1803])).
% 5.95/2.10  tff(c_1818, plain, (v1_xboole_0('#skF_5') | r2_hidden('#skF_1'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_146])).
% 5.95/2.10  tff(c_1824, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_314, c_1818])).
% 5.95/2.10  tff(c_1835, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1824, c_2])).
% 5.95/2.10  tff(c_111, plain, (![A_41, B_42]: (m1_subset_1('#skF_2'(A_41, B_42), A_41) | v1_xboole_0(A_41) | r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_100, c_22])).
% 5.95/2.10  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.95/2.10  tff(c_272, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_247])).
% 5.95/2.10  tff(c_3478, plain, (![B_273, B_274, A_275]: (r2_hidden(B_273, B_274) | ~r1_tarski(A_275, B_274) | ~m1_subset_1(B_273, A_275) | v1_xboole_0(A_275))), inference(resolution, [status(thm)], [c_24, c_293])).
% 5.95/2.10  tff(c_3490, plain, (![B_273]: (r2_hidden(B_273, '#skF_3') | ~m1_subset_1(B_273, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_272, c_3478])).
% 5.95/2.10  tff(c_3538, plain, (![B_277]: (r2_hidden(B_277, '#skF_3') | ~m1_subset_1(B_277, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1835, c_3490])).
% 5.95/2.10  tff(c_3549, plain, (![B_277]: (m1_subset_1(B_277, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_277, '#skF_4'))), inference(resolution, [status(thm)], [c_3538, c_22])).
% 5.95/2.10  tff(c_3591, plain, (![B_279]: (m1_subset_1(B_279, '#skF_3') | ~m1_subset_1(B_279, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_287, c_3549])).
% 5.95/2.10  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.95/2.10  tff(c_40, plain, (![D_22]: (r2_hidden(D_22, '#skF_5') | ~r2_hidden(D_22, '#skF_4') | ~m1_subset_1(D_22, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.95/2.10  tff(c_120, plain, (![A_46, B_47]: (~r2_hidden('#skF_2'(A_46, B_47), B_47) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.95/2.10  tff(c_3143, plain, (![A_255]: (r1_tarski(A_255, '#skF_5') | ~r2_hidden('#skF_2'(A_255, '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_2'(A_255, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_120])).
% 5.95/2.10  tff(c_3158, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_10, c_3143])).
% 5.95/2.10  tff(c_3201, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_3158])).
% 5.95/2.10  tff(c_3606, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_3591, c_3201])).
% 5.95/2.10  tff(c_3617, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_111, c_3606])).
% 5.95/2.10  tff(c_3623, plain, (r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1835, c_3617])).
% 5.95/2.10  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.95/2.10  tff(c_3639, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_3623, c_12])).
% 5.95/2.10  tff(c_3651, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_3639])).
% 5.95/2.10  tff(c_3492, plain, (![B_273]: (r2_hidden(B_273, '#skF_3') | ~m1_subset_1(B_273, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_271, c_3478])).
% 5.95/2.10  tff(c_3516, plain, (![B_276]: (r2_hidden(B_276, '#skF_3') | ~m1_subset_1(B_276, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_314, c_3492])).
% 5.95/2.10  tff(c_3527, plain, (![B_276]: (m1_subset_1(B_276, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_276, '#skF_5'))), inference(resolution, [status(thm)], [c_3516, c_22])).
% 5.95/2.10  tff(c_3560, plain, (![B_278]: (m1_subset_1(B_278, '#skF_3') | ~m1_subset_1(B_278, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_287, c_3527])).
% 5.95/2.10  tff(c_3564, plain, (![B_42]: (m1_subset_1('#skF_2'('#skF_5', B_42), '#skF_3') | v1_xboole_0('#skF_5') | r1_tarski('#skF_5', B_42))), inference(resolution, [status(thm)], [c_111, c_3560])).
% 5.95/2.10  tff(c_3806, plain, (![B_288]: (m1_subset_1('#skF_2'('#skF_5', B_288), '#skF_3') | r1_tarski('#skF_5', B_288))), inference(negUnitSimplification, [status(thm)], [c_314, c_3564])).
% 5.95/2.10  tff(c_3322, plain, (![B_267]: (r2_hidden('#skF_2'('#skF_5', B_267), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_5', B_267), '#skF_3') | r1_tarski('#skF_5', B_267))), inference(resolution, [status(thm)], [c_10, c_132])).
% 5.95/2.10  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.95/2.10  tff(c_3349, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_3') | r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_3322, c_8])).
% 5.95/2.10  tff(c_3354, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_3349])).
% 5.95/2.10  tff(c_3809, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_3806, c_3354])).
% 5.95/2.10  tff(c_3820, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3651, c_3809])).
% 5.95/2.10  tff(c_3821, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_3349])).
% 5.95/2.10  tff(c_3835, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_3821, c_12])).
% 5.95/2.10  tff(c_3844, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_32, c_3835])).
% 5.95/2.10  tff(c_3944, plain, (![B_293, B_294, A_295]: (r2_hidden(B_293, B_294) | ~r1_tarski(A_295, B_294) | ~m1_subset_1(B_293, A_295) | v1_xboole_0(A_295))), inference(resolution, [status(thm)], [c_24, c_293])).
% 5.95/2.10  tff(c_3958, plain, (![B_293]: (r2_hidden(B_293, '#skF_3') | ~m1_subset_1(B_293, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_272, c_3944])).
% 5.95/2.10  tff(c_4042, plain, (![B_298]: (r2_hidden(B_298, '#skF_3') | ~m1_subset_1(B_298, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1835, c_3958])).
% 5.95/2.10  tff(c_4053, plain, (![B_298]: (m1_subset_1(B_298, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_298, '#skF_4'))), inference(resolution, [status(thm)], [c_4042, c_22])).
% 5.95/2.10  tff(c_4125, plain, (![B_301]: (m1_subset_1(B_301, '#skF_3') | ~m1_subset_1(B_301, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_287, c_4053])).
% 5.95/2.10  tff(c_4136, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_4125, c_3201])).
% 5.95/2.10  tff(c_4143, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_111, c_4136])).
% 5.95/2.10  tff(c_4150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3844, c_1835, c_4143])).
% 5.95/2.10  tff(c_4151, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_3158])).
% 5.95/2.10  tff(c_4191, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_4151, c_12])).
% 5.95/2.10  tff(c_4202, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_4191])).
% 5.95/2.10  tff(c_4153, plain, (![B_302, B_303, A_304]: (r2_hidden(B_302, B_303) | ~r1_tarski(A_304, B_303) | ~m1_subset_1(B_302, A_304) | v1_xboole_0(A_304))), inference(resolution, [status(thm)], [c_24, c_293])).
% 5.95/2.10  tff(c_4159, plain, (![B_302]: (r2_hidden(B_302, '#skF_3') | ~m1_subset_1(B_302, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_271, c_4153])).
% 5.95/2.10  tff(c_4272, plain, (![B_307]: (r2_hidden(B_307, '#skF_3') | ~m1_subset_1(B_307, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_314, c_4159])).
% 5.95/2.10  tff(c_4281, plain, (![B_307]: (m1_subset_1(B_307, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_307, '#skF_5'))), inference(resolution, [status(thm)], [c_4272, c_22])).
% 5.95/2.10  tff(c_4392, plain, (![B_314]: (m1_subset_1(B_314, '#skF_3') | ~m1_subset_1(B_314, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_287, c_4281])).
% 5.95/2.10  tff(c_4399, plain, (![B_42]: (m1_subset_1('#skF_2'('#skF_5', B_42), '#skF_3') | v1_xboole_0('#skF_5') | r1_tarski('#skF_5', B_42))), inference(resolution, [status(thm)], [c_111, c_4392])).
% 5.95/2.10  tff(c_4678, plain, (![B_330]: (m1_subset_1('#skF_2'('#skF_5', B_330), '#skF_3') | r1_tarski('#skF_5', B_330))), inference(negUnitSimplification, [status(thm)], [c_314, c_4399])).
% 5.95/2.10  tff(c_4211, plain, (![B_305]: (r2_hidden('#skF_2'('#skF_5', B_305), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_5', B_305), '#skF_3') | r1_tarski('#skF_5', B_305))), inference(resolution, [status(thm)], [c_10, c_132])).
% 5.95/2.10  tff(c_4226, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_3') | r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_4211, c_8])).
% 5.95/2.10  tff(c_4240, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_4202, c_4202, c_4226])).
% 5.95/2.10  tff(c_4681, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_4678, c_4240])).
% 5.95/2.10  tff(c_4692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4202, c_4681])).
% 5.95/2.10  tff(c_4704, plain, (![D_332]: (~r2_hidden(D_332, '#skF_4') | ~m1_subset_1(D_332, '#skF_3'))), inference(splitRight, [status(thm)], [c_67])).
% 5.95/2.10  tff(c_4717, plain, (![B_16]: (~m1_subset_1(B_16, '#skF_3') | ~m1_subset_1(B_16, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_4704])).
% 5.95/2.10  tff(c_4727, plain, (![B_333]: (~m1_subset_1(B_333, '#skF_3') | ~m1_subset_1(B_333, '#skF_4'))), inference(splitLeft, [status(thm)], [c_4717])).
% 5.95/2.10  tff(c_4731, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_99, c_4727])).
% 5.95/2.10  tff(c_4738, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_287, c_4731])).
% 5.95/2.10  tff(c_4743, plain, (~v1_xboole_0('#skF_1'('#skF_3')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_4738])).
% 5.95/2.10  tff(c_4744, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_4743])).
% 5.95/2.10  tff(c_5330, plain, (![B_382, B_383, A_384]: (r2_hidden(B_382, B_383) | ~r1_tarski(A_384, B_383) | ~m1_subset_1(B_382, A_384) | v1_xboole_0(A_384))), inference(resolution, [status(thm)], [c_24, c_293])).
% 5.95/2.10  tff(c_5338, plain, (![B_382]: (r2_hidden(B_382, '#skF_3') | ~m1_subset_1(B_382, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_272, c_5330])).
% 5.95/2.10  tff(c_5362, plain, (![B_385]: (r2_hidden(B_385, '#skF_3') | ~m1_subset_1(B_385, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_4744, c_5338])).
% 5.95/2.10  tff(c_5371, plain, (![B_385]: (m1_subset_1(B_385, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_385, '#skF_4'))), inference(resolution, [status(thm)], [c_5362, c_22])).
% 5.95/2.10  tff(c_5381, plain, (![B_386]: (m1_subset_1(B_386, '#skF_3') | ~m1_subset_1(B_386, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_287, c_5371])).
% 5.95/2.10  tff(c_4725, plain, (![B_16]: (~m1_subset_1(B_16, '#skF_3') | ~m1_subset_1(B_16, '#skF_4'))), inference(splitLeft, [status(thm)], [c_4717])).
% 5.95/2.10  tff(c_5421, plain, (![B_387]: (~m1_subset_1(B_387, '#skF_4'))), inference(resolution, [status(thm)], [c_5381, c_4725])).
% 5.95/2.10  tff(c_5429, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_99, c_5421])).
% 5.95/2.10  tff(c_5440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4744, c_5429])).
% 5.95/2.10  tff(c_5442, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_4743])).
% 5.95/2.10  tff(c_4694, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_67])).
% 5.95/2.10  tff(c_163, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_113, c_147])).
% 5.95/2.10  tff(c_176, plain, (![B_42, A_41]: (B_42=A_41 | ~v1_xboole_0(B_42) | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_113, c_163])).
% 5.95/2.10  tff(c_4697, plain, (![A_41]: (A_41='#skF_5' | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_4694, c_176])).
% 5.95/2.10  tff(c_5446, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_5442, c_4697])).
% 5.95/2.10  tff(c_5452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_5446])).
% 5.95/2.10  tff(c_5453, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_4717])).
% 5.95/2.10  tff(c_5456, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_5453, c_4697])).
% 5.95/2.10  tff(c_5462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_5456])).
% 5.95/2.10  tff(c_5463, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_278])).
% 5.95/2.10  tff(c_5469, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5463, c_32])).
% 5.95/2.10  tff(c_5464, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_278])).
% 5.95/2.10  tff(c_285, plain, ('#skF_3'='#skF_4' | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_272, c_156])).
% 5.95/2.10  tff(c_5492, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5464, c_285])).
% 5.95/2.10  tff(c_5493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5469, c_5492])).
% 5.95/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.95/2.10  
% 5.95/2.10  Inference rules
% 5.95/2.10  ----------------------
% 5.95/2.10  #Ref     : 0
% 5.95/2.10  #Sup     : 1169
% 5.95/2.10  #Fact    : 0
% 5.95/2.10  #Define  : 0
% 5.95/2.10  #Split   : 23
% 5.95/2.10  #Chain   : 0
% 5.95/2.10  #Close   : 0
% 5.95/2.10  
% 5.95/2.10  Ordering : KBO
% 5.95/2.10  
% 5.95/2.10  Simplification rules
% 5.95/2.10  ----------------------
% 5.95/2.10  #Subsume      : 378
% 5.95/2.10  #Demod        : 150
% 5.95/2.10  #Tautology    : 138
% 5.95/2.10  #SimpNegUnit  : 221
% 5.95/2.10  #BackRed      : 5
% 5.95/2.10  
% 5.95/2.10  #Partial instantiations: 0
% 5.95/2.10  #Strategies tried      : 1
% 5.95/2.10  
% 5.95/2.10  Timing (in seconds)
% 5.95/2.10  ----------------------
% 5.95/2.10  Preprocessing        : 0.28
% 5.95/2.10  Parsing              : 0.15
% 5.95/2.10  CNF conversion       : 0.02
% 5.95/2.10  Main loop            : 1.03
% 5.95/2.10  Inferencing          : 0.38
% 5.95/2.10  Reduction            : 0.28
% 5.95/2.10  Demodulation         : 0.17
% 5.95/2.10  BG Simplification    : 0.03
% 5.95/2.10  Subsumption          : 0.25
% 5.95/2.10  Abstraction          : 0.05
% 5.95/2.10  MUC search           : 0.00
% 5.95/2.10  Cooper               : 0.00
% 5.95/2.10  Total                : 1.36
% 5.95/2.10  Index Insertion      : 0.00
% 5.95/2.10  Index Deletion       : 0.00
% 5.95/2.10  Index Matching       : 0.00
% 5.95/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
