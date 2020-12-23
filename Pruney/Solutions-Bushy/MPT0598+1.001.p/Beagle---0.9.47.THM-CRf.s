%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0598+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:33 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   45 (  62 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 114 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A) )
       => ! [C] :
            ( r2_hidden(C,k2_relat_1(B))
           => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_29,plain,(
    ! [A_18,B_19] :
      ( r2_hidden(A_18,B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_33,plain,
    ( v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_29,c_16])).

tff(c_34,plain,(
    ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_20,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_18,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_65,plain,(
    ! [A_32,C_33,B_34] :
      ( m1_subset_1(A_32,C_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(C_33))
      | ~ r2_hidden(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    ! [A_35,B_36,A_37] :
      ( m1_subset_1(A_35,B_36)
      | ~ r2_hidden(A_35,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(resolution,[status(thm)],[c_10,c_65])).

tff(c_76,plain,(
    ! [B_38] :
      ( m1_subset_1('#skF_3',B_38)
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_38) ) ),
    inference(resolution,[status(thm)],[c_18,c_69])).

tff(c_80,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_3',A_1)
      | ~ v5_relat_1('#skF_2',A_1)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4,c_76])).

tff(c_84,plain,(
    ! [A_39] :
      ( m1_subset_1('#skF_3',A_39)
      | ~ v5_relat_1('#skF_2',A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_80])).

tff(c_87,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_84])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_87])).

tff(c_92,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_106,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(k2_relat_1(B_47),A_48)
      | ~ v5_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_94,plain,(
    ! [C_40,B_41,A_42] :
      ( ~ v1_xboole_0(C_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_98,plain,(
    ! [B_43,A_44,A_45] :
      ( ~ v1_xboole_0(B_43)
      | ~ r2_hidden(A_44,A_45)
      | ~ r1_tarski(A_45,B_43) ) ),
    inference(resolution,[status(thm)],[c_10,c_94])).

tff(c_104,plain,(
    ! [B_43] :
      ( ~ v1_xboole_0(B_43)
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_43) ) ),
    inference(resolution,[status(thm)],[c_18,c_98])).

tff(c_110,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(A_48)
      | ~ v5_relat_1('#skF_2',A_48)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_106,c_104])).

tff(c_114,plain,(
    ! [A_49] :
      ( ~ v1_xboole_0(A_49)
      | ~ v5_relat_1('#skF_2',A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_110])).

tff(c_117,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_114])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_117])).

%------------------------------------------------------------------------------
