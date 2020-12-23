%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0369+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:11 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   42 (  54 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 103 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_57,plain,(
    ! [B_25,A_26] :
      ( v1_xboole_0(B_25)
      | ~ m1_subset_1(B_25,A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_131,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k3_subset_1(A_41,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_140,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_131])).

tff(c_178,plain,(
    ! [D_48,A_49,B_50] :
      ( r2_hidden(D_48,k4_xboole_0(A_49,B_50))
      | r2_hidden(D_48,B_50)
      | ~ r2_hidden(D_48,A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_212,plain,(
    ! [D_52] :
      ( r2_hidden(D_52,k3_subset_1('#skF_3','#skF_4'))
      | r2_hidden(D_52,'#skF_4')
      | ~ r2_hidden(D_52,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_178])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_227,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_212,c_36])).

tff(c_239,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_227])).

tff(c_243,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_239])).

tff(c_246,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_243])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_246])).

tff(c_250,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_32,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_257,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_250,c_32])).

tff(c_261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_257])).

%------------------------------------------------------------------------------
