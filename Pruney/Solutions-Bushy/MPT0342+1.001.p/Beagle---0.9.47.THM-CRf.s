%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0342+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:08 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 122 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 313 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                   => r2_hidden(D,C) ) )
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_20,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_1'(A_26,B_27),A_26)
      | r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( ~ v1_xboole_0(B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_54,plain,(
    ! [A_28,B_29] :
      ( ~ v1_xboole_0(A_28)
      | r1_tarski(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_44,c_18])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_20])).

tff(c_14,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_66,plain,(
    ! [B_33,A_34] :
      ( m1_subset_1(B_33,A_34)
      | ~ r2_hidden(B_33,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1('#skF_1'(A_3,B_4),A_3)
      | v1_xboole_0(A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_14,c_66])).

tff(c_6,plain,(
    ! [B_2,A_1] :
      ( m1_subset_1(B_2,A_1)
      | ~ v1_xboole_0(B_2)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [D_18] :
      ( r2_hidden(D_18,'#skF_4')
      | ~ r2_hidden(D_18,'#skF_3')
      | ~ m1_subset_1(D_18,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_116,plain,(
    ! [B_41] :
      ( r2_hidden('#skF_1'('#skF_3',B_41),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_41),'#skF_2')
      | r1_tarski('#skF_3',B_41) ) ),
    inference(resolution,[status(thm)],[c_44,c_22])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_125,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_116,c_12])).

tff(c_133,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_20,c_125])).

tff(c_138,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_3','#skF_4'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_133])).

tff(c_139,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_141,plain,(
    ! [C_42,A_43,B_44] :
      ( r2_hidden(C_42,A_43)
      | ~ r2_hidden(C_42,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_255,plain,(
    ! [B_63,A_64,A_65] :
      ( r2_hidden(B_63,A_64)
      | ~ m1_subset_1(A_65,k1_zfmisc_1(A_64))
      | ~ m1_subset_1(B_63,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_4,c_141])).

tff(c_265,plain,(
    ! [B_63] :
      ( r2_hidden(B_63,'#skF_2')
      | ~ m1_subset_1(B_63,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_255])).

tff(c_274,plain,(
    ! [B_66] :
      ( r2_hidden(B_66,'#skF_2')
      | ~ m1_subset_1(B_66,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_265])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( m1_subset_1(B_2,A_1)
      | ~ r2_hidden(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_281,plain,(
    ! [B_66] :
      ( m1_subset_1(B_66,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_66,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_274,c_2])).

tff(c_318,plain,(
    ! [B_68] :
      ( m1_subset_1(B_68,'#skF_2')
      | ~ m1_subset_1(B_68,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_281])).

tff(c_340,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_318,c_133])).

tff(c_366,plain,
    ( v1_xboole_0('#skF_3')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_340])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_58,c_366])).

tff(c_375,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_377,plain,(
    ! [C_71,A_72,B_73] :
      ( r2_hidden(C_71,A_72)
      | ~ r2_hidden(C_71,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_482,plain,(
    ! [A_90,B_91,A_92] :
      ( r2_hidden('#skF_1'(A_90,B_91),A_92)
      | ~ m1_subset_1(A_90,k1_zfmisc_1(A_92))
      | r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_14,c_377])).

tff(c_507,plain,(
    ! [A_93,A_94] :
      ( ~ m1_subset_1(A_93,k1_zfmisc_1(A_94))
      | r1_tarski(A_93,A_94) ) ),
    inference(resolution,[status(thm)],[c_482,c_12])).

tff(c_525,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_507])).

tff(c_92,plain,(
    ! [C_37,B_38,A_39] :
      ( r2_hidden(C_37,B_38)
      | ~ r2_hidden(C_37,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_415,plain,(
    ! [A_79,B_80,B_81] :
      ( r2_hidden('#skF_1'(A_79,B_80),B_81)
      | ~ r1_tarski(A_79,B_81)
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_14,c_92])).

tff(c_439,plain,(
    ! [B_81,A_79,B_80] :
      ( ~ v1_xboole_0(B_81)
      | ~ r1_tarski(A_79,B_81)
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_415,c_18])).

tff(c_539,plain,(
    ! [B_80] :
      ( ~ v1_xboole_0('#skF_2')
      | r1_tarski('#skF_3',B_80) ) ),
    inference(resolution,[status(thm)],[c_525,c_439])).

tff(c_545,plain,(
    ! [B_80] : r1_tarski('#skF_3',B_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_539])).

tff(c_584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_20])).

%------------------------------------------------------------------------------
