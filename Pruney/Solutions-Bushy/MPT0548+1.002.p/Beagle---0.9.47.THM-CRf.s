%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0548+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:28 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   49 (  74 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :   15
%              Number of atoms          :   66 ( 113 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > o_1_3_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(o_1_3_relat_1,type,(
    o_1_3_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(o_1_3_relat_1(A),k9_relat_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_1_3_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_44,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_62,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_22,plain,(
    ! [A_44] : m1_subset_1(o_1_3_relat_1(A_44),k9_relat_1(k1_xboole_0,A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [A_45,B_46] :
      ( r2_hidden(A_45,B_46)
      | v1_xboole_0(B_46)
      | ~ m1_subset_1(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_33,plain,(
    ! [A_50] :
      ( v1_relat_1(A_50)
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_37,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_33])).

tff(c_302,plain,(
    ! [A_88,B_89,D_90] :
      ( r2_hidden(k4_tarski('#skF_4'(A_88,B_89,k9_relat_1(A_88,B_89),D_90),D_90),A_88)
      | ~ r2_hidden(D_90,k9_relat_1(A_88,B_89))
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,(
    ! [A_61,B_62,D_63] :
      ( r2_hidden('#skF_4'(A_61,B_62,k9_relat_1(A_61,B_62),D_63),B_62)
      | ~ r2_hidden(D_63,k9_relat_1(A_61,B_62))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [B_49,A_48] :
      ( ~ v1_xboole_0(B_49)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_63,plain,(
    ! [B_64,D_65,A_66] :
      ( ~ v1_xboole_0(B_64)
      | ~ r2_hidden(D_65,k9_relat_1(A_66,B_64))
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_55,c_30])).

tff(c_85,plain,(
    ! [B_71,A_72,A_73] :
      ( ~ v1_xboole_0(B_71)
      | ~ v1_relat_1(A_72)
      | v1_xboole_0(k9_relat_1(A_72,B_71))
      | ~ m1_subset_1(A_73,k9_relat_1(A_72,B_71)) ) ),
    inference(resolution,[status(thm)],[c_26,c_63])).

tff(c_88,plain,(
    ! [A_44] :
      ( ~ v1_xboole_0(A_44)
      | ~ v1_relat_1(k1_xboole_0)
      | v1_xboole_0(k9_relat_1(k1_xboole_0,A_44)) ) ),
    inference(resolution,[status(thm)],[c_22,c_85])).

tff(c_92,plain,(
    ! [A_74] :
      ( ~ v1_xboole_0(A_74)
      | v1_xboole_0(k9_relat_1(k1_xboole_0,A_74)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_88])).

tff(c_28,plain,(
    ! [A_47] :
      ( k1_xboole_0 = A_47
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_101,plain,(
    ! [A_75] :
      ( k9_relat_1(k1_xboole_0,A_75) = k1_xboole_0
      | ~ v1_xboole_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_92,c_28])).

tff(c_109,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_101])).

tff(c_62,plain,(
    ! [B_62,D_63,A_61] :
      ( ~ v1_xboole_0(B_62)
      | ~ r2_hidden(D_63,k9_relat_1(A_61,B_62))
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_55,c_30])).

tff(c_157,plain,(
    ! [D_63] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_63,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_62])).

tff(c_173,plain,(
    ! [D_63] : ~ r2_hidden(D_63,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_24,c_157])).

tff(c_310,plain,(
    ! [D_90,B_89] :
      ( ~ r2_hidden(D_90,k9_relat_1(k1_xboole_0,B_89))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_302,c_173])).

tff(c_344,plain,(
    ! [D_91,B_92] : ~ r2_hidden(D_91,k9_relat_1(k1_xboole_0,B_92)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_310])).

tff(c_490,plain,(
    ! [B_102,A_103] :
      ( v1_xboole_0(k9_relat_1(k1_xboole_0,B_102))
      | ~ m1_subset_1(A_103,k9_relat_1(k1_xboole_0,B_102)) ) ),
    inference(resolution,[status(thm)],[c_26,c_344])).

tff(c_504,plain,(
    ! [A_104] : v1_xboole_0(k9_relat_1(k1_xboole_0,A_104)) ),
    inference(resolution,[status(thm)],[c_22,c_490])).

tff(c_519,plain,(
    ! [A_104] : k9_relat_1(k1_xboole_0,A_104) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_504,c_28])).

tff(c_32,plain,(
    k9_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_32])).

%------------------------------------------------------------------------------
