%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0828+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:54 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  81 expanded)
%              Number of equality atoms :    6 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(c_18,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_49,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_51,plain,(
    ! [A_19,B_20,C_21] :
      ( m1_subset_1(k1_relset_1(A_19,B_20,C_21),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    ! [A_22,B_23,C_24] :
      ( r1_tarski(k1_relset_1(A_22,B_23,C_24),A_22)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(resolution,[status(thm)],[c_51,c_14])).

tff(c_67,plain,(
    r1_tarski(k1_relset_1('#skF_2','#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_56])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_77,plain,
    ( k1_relset_1('#skF_2','#skF_1','#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_67,c_2])).

tff(c_80,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_77])).

tff(c_20,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,(
    ! [C_39,A_40,B_41,D_42] :
      ( r1_tarski(C_39,k1_relset_1(A_40,B_41,D_42))
      | ~ r1_tarski(k6_relat_1(C_39),D_42)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_115,plain,(
    ! [A_43,B_44] :
      ( r1_tarski('#skF_2',k1_relset_1(A_43,B_44,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(resolution,[status(thm)],[c_20,c_107])).

tff(c_121,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_115])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_121])).

tff(c_127,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_221,plain,(
    ! [C_71,A_72,B_73,D_74] :
      ( r1_tarski(C_71,k2_relset_1(A_72,B_73,D_74))
      | ~ r1_tarski(k6_relat_1(C_71),D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_229,plain,(
    ! [A_75,B_76] :
      ( r1_tarski('#skF_2',k2_relset_1(A_75,B_76,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(resolution,[status(thm)],[c_20,c_221])).

tff(c_235,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_229])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_235])).

%------------------------------------------------------------------------------
