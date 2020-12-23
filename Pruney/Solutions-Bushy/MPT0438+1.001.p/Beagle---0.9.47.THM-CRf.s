%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0438+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:18 EST 2020

% Result     : Theorem 13.73s
% Output     : CNFRefutation 13.79s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  60 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_3 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_136,plain,(
    ! [A_96,B_97] :
      ( r2_hidden(k4_tarski('#skF_1'(A_96,B_97),'#skF_2'(A_96,B_97)),A_96)
      | r1_tarski(A_96,B_97)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [C_33,A_18,D_36] :
      ( r2_hidden(C_33,k1_relat_1(A_18))
      | ~ r2_hidden(k4_tarski(C_33,D_36),A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_164,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_1'(A_96,B_97),k1_relat_1(A_96))
      | r1_tarski(A_96,B_97)
      | ~ v1_relat_1(A_96) ) ),
    inference(resolution,[status(thm)],[c_136,c_10])).

tff(c_22,plain,(
    ! [C_52,A_37,D_55] :
      ( r2_hidden(C_52,k2_relat_1(A_37))
      | ~ r2_hidden(k4_tarski(D_55,C_52),A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_163,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_2'(A_96,B_97),k2_relat_1(A_96))
      | r1_tarski(A_96,B_97)
      | ~ v1_relat_1(A_96) ) ),
    inference(resolution,[status(thm)],[c_136,c_22])).

tff(c_32,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( r2_hidden(k4_tarski(A_56,B_57),k2_zfmisc_1(C_58,D_59))
      | ~ r2_hidden(B_57,D_59)
      | ~ r2_hidden(A_56,C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_202,plain,(
    ! [A_106,B_107] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_106,B_107),'#skF_2'(A_106,B_107)),B_107)
      | r1_tarski(A_106,B_107)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_20462,plain,(
    ! [A_689,C_690,D_691] :
      ( r1_tarski(A_689,k2_zfmisc_1(C_690,D_691))
      | ~ v1_relat_1(A_689)
      | ~ r2_hidden('#skF_2'(A_689,k2_zfmisc_1(C_690,D_691)),D_691)
      | ~ r2_hidden('#skF_1'(A_689,k2_zfmisc_1(C_690,D_691)),C_690) ) ),
    inference(resolution,[status(thm)],[c_32,c_202])).

tff(c_24199,plain,(
    ! [A_732,C_733] :
      ( ~ r2_hidden('#skF_1'(A_732,k2_zfmisc_1(C_733,k2_relat_1(A_732))),C_733)
      | r1_tarski(A_732,k2_zfmisc_1(C_733,k2_relat_1(A_732)))
      | ~ v1_relat_1(A_732) ) ),
    inference(resolution,[status(thm)],[c_163,c_20462])).

tff(c_24431,plain,(
    ! [A_734] :
      ( r1_tarski(A_734,k2_zfmisc_1(k1_relat_1(A_734),k2_relat_1(A_734)))
      | ~ v1_relat_1(A_734) ) ),
    inference(resolution,[status(thm)],[c_164,c_24199])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_11',k2_zfmisc_1(k1_relat_1('#skF_11'),k2_relat_1('#skF_11'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24449,plain,(
    ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_24431,c_38])).

tff(c_24472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_24449])).

%------------------------------------------------------------------------------
