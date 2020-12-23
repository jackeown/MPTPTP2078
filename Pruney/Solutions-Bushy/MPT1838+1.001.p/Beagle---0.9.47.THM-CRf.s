%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1838+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:30 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   42 (  80 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   75 ( 208 expanded)
%              Number of equality atoms :   25 (  61 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_34,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_35,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    ! [A_16,B_17] :
      ( k6_domain_1(A_16,B_17) = k1_tarski(B_17)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,(
    ! [A_20] :
      ( k6_domain_1(A_20,'#skF_1'(A_20)) = k1_tarski('#skF_1'(A_20))
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_4,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_75,plain,(
    ! [A_21] :
      ( k1_tarski('#skF_1'(A_21)) = A_21
      | ~ v1_zfmisc_1(A_21)
      | v1_xboole_0(A_21)
      | ~ v1_zfmisc_1(A_21)
      | v1_xboole_0(A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_4])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( k1_tarski(B_8) = A_7
      | k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_tarski(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_119,plain,(
    ! [A_25,A_26] :
      ( k1_tarski('#skF_1'(A_25)) = A_26
      | k1_xboole_0 = A_26
      | ~ r1_tarski(A_26,A_25)
      | ~ v1_zfmisc_1(A_25)
      | v1_xboole_0(A_25)
      | ~ v1_zfmisc_1(A_25)
      | v1_xboole_0(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_12])).

tff(c_131,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_119])).

tff(c_142,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_131])).

tff(c_143,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_142])).

tff(c_144,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_149,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_8])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_149])).

tff(c_152,plain,(
    k1_tarski('#skF_1'('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_66,plain,(
    ! [A_20] :
      ( k1_tarski('#skF_1'(A_20)) = A_20
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20)
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_4])).

tff(c_163,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_66])).

tff(c_187,plain,
    ( '#skF_2' = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_163])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_18,c_187])).

%------------------------------------------------------------------------------
