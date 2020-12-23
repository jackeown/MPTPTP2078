%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0816+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:53 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  56 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( r1_tarski(k1_relat_1(C),A)
            & r1_tarski(k2_relat_1(C),B) )
         => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_30,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_19,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_23,plain,(
    ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_19,c_12])).

tff(c_16,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_8] :
      ( r1_tarski(A_8,k2_zfmisc_1(k1_relat_1(A_8),k2_relat_1(A_8)))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    ! [A_23,C_24,B_25,D_26] :
      ( r1_tarski(k2_zfmisc_1(A_23,C_24),k2_zfmisc_1(B_25,D_26))
      | ~ r1_tarski(C_24,D_26)
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_73,plain,(
    ! [A_35,D_33,A_34,C_32,B_31] :
      ( r1_tarski(A_34,k2_zfmisc_1(B_31,D_33))
      | ~ r1_tarski(A_34,k2_zfmisc_1(A_35,C_32))
      | ~ r1_tarski(C_32,D_33)
      | ~ r1_tarski(A_35,B_31) ) ),
    inference(resolution,[status(thm)],[c_46,c_4])).

tff(c_96,plain,(
    ! [A_37,B_38,D_39] :
      ( r1_tarski(A_37,k2_zfmisc_1(B_38,D_39))
      | ~ r1_tarski(k2_relat_1(A_37),D_39)
      | ~ r1_tarski(k1_relat_1(A_37),B_38)
      | ~ v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_106,plain,(
    ! [B_38] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(B_38,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_38)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_96])).

tff(c_115,plain,(
    ! [B_40] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(B_40,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_106])).

tff(c_129,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_115])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23,c_129])).

%------------------------------------------------------------------------------
