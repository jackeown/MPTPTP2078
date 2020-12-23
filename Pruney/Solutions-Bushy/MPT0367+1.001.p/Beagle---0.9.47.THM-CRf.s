%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0367+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:11 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   29 (  36 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    4
%              Number of atoms          :   41 (  64 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,B)
                 => r2_hidden(D,C) )
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
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

tff(c_18,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_63,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_1'(A_26,B_27),A_26)
      | r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( ~ v1_xboole_0(B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_89,plain,(
    ! [A_31,B_32] :
      ( ~ v1_xboole_0(A_31)
      | r1_tarski(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_63,c_16])).

tff(c_93,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_89,c_18])).

tff(c_14,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74,plain,(
    ! [B_29,A_30] :
      ( m1_subset_1(B_29,A_30)
      | ~ r2_hidden(B_29,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_189,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1('#skF_1'(A_50,B_51),A_50)
      | v1_xboole_0(A_50)
      | r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_14,c_74])).

tff(c_20,plain,(
    ! [D_14] :
      ( r2_hidden(D_14,'#skF_4')
      | ~ m1_subset_1(D_14,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_47,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden('#skF_1'(A_22,B_23),B_23)
      | r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_52,plain,(
    ! [A_22] :
      ( r1_tarski(A_22,'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_22,'#skF_4'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_47])).

tff(c_201,plain,
    ( v1_xboole_0('#skF_3')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_52])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_93,c_18,c_201])).

%------------------------------------------------------------------------------
