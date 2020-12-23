%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:40 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 145 expanded)
%              Number of leaves         :   52 (  74 expanded)
%              Depth                    :    8
%              Number of atoms          :  107 ( 191 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k9_setfam_1 > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_funcop_1,type,(
    k2_funcop_1: ( $i * $i ) > $i )).

tff(k7_funcop_1,type,(
    k7_funcop_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_yellow_1,type,(
    k5_yellow_1: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_yellow_1,type,(
    k6_yellow_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(v1_yellow_1,type,(
    v1_yellow_1: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_98,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_100,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_86,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_72,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_71,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

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

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_68,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_60,plain,(
    ! [A_51] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_51)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_91,plain,(
    ! [A_58] :
      ( k1_xboole_0 = A_58
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_98,plain,(
    ! [A_51] : k2_funcop_1(k1_xboole_0,A_51) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_62,plain,(
    ! [A_52,B_53] : k7_funcop_1(A_52,B_53) = k2_funcop_1(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_56,plain,(
    ! [A_47,B_48] :
      ( k5_yellow_1(A_47,k7_funcop_1(A_47,B_48)) = k6_yellow_1(A_47,B_48)
      | ~ l1_orders_2(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_293,plain,(
    ! [A_99,B_100] :
      ( k5_yellow_1(A_99,k2_funcop_1(A_99,B_100)) = k6_yellow_1(A_99,B_100)
      | ~ l1_orders_2(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56])).

tff(c_323,plain,(
    ! [A_103] :
      ( k6_yellow_1(k1_xboole_0,A_103) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_293])).

tff(c_327,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_3') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_68,c_323])).

tff(c_66,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_328,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_66])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_101,plain,(
    ! [A_59] :
      ( v1_relat_1(A_59)
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_109,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_101])).

tff(c_119,plain,(
    ! [A_61] : k6_relat_1(A_61) = k6_partfun1(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_125,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_42])).

tff(c_52,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_46,plain,(
    ! [A_42] : v1_funct_1(k6_relat_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_70,plain,(
    ! [A_42] : v1_funct_1(k6_partfun1(A_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46])).

tff(c_137,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_70])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_196,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_2'(A_75,B_76),A_75)
      | r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_205,plain,(
    ! [A_75,B_76] :
      ( ~ v1_xboole_0(A_75)
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_196,c_2])).

tff(c_215,plain,(
    ! [B_83,A_84] :
      ( v4_relat_1(B_83,A_84)
      | ~ r1_tarski(k1_relat_1(B_83),A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_265,plain,(
    ! [B_90,B_91] :
      ( v4_relat_1(B_90,B_91)
      | ~ v1_relat_1(B_90)
      | ~ v1_xboole_0(k1_relat_1(B_90)) ) ),
    inference(resolution,[status(thm)],[c_205,c_215])).

tff(c_267,plain,(
    ! [B_91] :
      ( v4_relat_1(k1_xboole_0,B_91)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_265])).

tff(c_269,plain,(
    ! [B_91] : v4_relat_1(k1_xboole_0,B_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_109,c_267])).

tff(c_333,plain,(
    ! [B_104] :
      ( v1_partfun1(B_104,k1_relat_1(B_104))
      | ~ v4_relat_1(B_104,k1_relat_1(B_104))
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_343,plain,
    ( v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_333])).

tff(c_349,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_269,c_40,c_343])).

tff(c_178,plain,(
    ! [A_69,B_70] :
      ( v1_yellow_1(k2_funcop_1(A_69,B_70))
      | ~ l1_orders_2(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_181,plain,(
    ! [A_51] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_178])).

tff(c_191,plain,(
    ! [A_51] : ~ l1_orders_2(A_51) ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_68])).

tff(c_194,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_641,plain,(
    ! [A_170] :
      ( k5_yellow_1(k1_xboole_0,A_170) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_170)
      | ~ v1_partfun1(A_170,k1_xboole_0)
      | ~ v1_funct_1(A_170)
      | ~ v4_relat_1(A_170,k1_xboole_0)
      | ~ v1_relat_1(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_644,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_269,c_641])).

tff(c_647,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_137,c_349,c_194,c_644])).

tff(c_649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_328,c_647])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.98  
% 3.96/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.98  %$ v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k9_setfam_1 > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 3.96/1.98  
% 3.96/1.98  %Foreground sorts:
% 3.96/1.98  
% 3.96/1.98  
% 3.96/1.98  %Background operators:
% 3.96/1.98  
% 3.96/1.98  
% 3.96/1.98  %Foreground operators:
% 3.96/1.98  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 3.96/1.98  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 3.96/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.96/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.98  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 3.96/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.96/1.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.96/1.98  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.96/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.96/1.98  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 3.96/1.98  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.96/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/1.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.96/1.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.96/1.98  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 3.96/1.98  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 3.96/1.98  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 3.96/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.96/1.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.96/1.98  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.96/1.98  tff('#skF_3', type, '#skF_3': $i).
% 3.96/1.98  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.96/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.96/1.98  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.96/1.98  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.96/1.98  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.96/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.96/1.98  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.96/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.96/1.98  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.96/1.98  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.96/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.96/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.96/1.98  
% 3.96/2.01  tff(f_117, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 3.96/2.01  tff(f_98, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 3.96/2.01  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.96/2.01  tff(f_100, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 3.96/2.01  tff(f_92, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 3.96/2.01  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.96/2.01  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.96/2.01  tff(f_86, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.96/2.01  tff(f_72, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 3.96/2.01  tff(f_76, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.96/2.01  tff(f_71, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.96/2.01  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.96/2.01  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.96/2.01  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.96/2.01  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.96/2.01  tff(f_96, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_yellow_1)).
% 3.96/2.01  tff(f_112, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 3.96/2.01  tff(c_68, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.96/2.01  tff(c_60, plain, (![A_51]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_51)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.96/2.01  tff(c_91, plain, (![A_58]: (k1_xboole_0=A_58 | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.96/2.01  tff(c_98, plain, (![A_51]: (k2_funcop_1(k1_xboole_0, A_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_91])).
% 3.96/2.01  tff(c_62, plain, (![A_52, B_53]: (k7_funcop_1(A_52, B_53)=k2_funcop_1(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.96/2.01  tff(c_56, plain, (![A_47, B_48]: (k5_yellow_1(A_47, k7_funcop_1(A_47, B_48))=k6_yellow_1(A_47, B_48) | ~l1_orders_2(B_48))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.96/2.01  tff(c_293, plain, (![A_99, B_100]: (k5_yellow_1(A_99, k2_funcop_1(A_99, B_100))=k6_yellow_1(A_99, B_100) | ~l1_orders_2(B_100))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56])).
% 3.96/2.01  tff(c_323, plain, (![A_103]: (k6_yellow_1(k1_xboole_0, A_103)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_103))), inference(superposition, [status(thm), theory('equality')], [c_98, c_293])).
% 3.96/2.01  tff(c_327, plain, (k6_yellow_1(k1_xboole_0, '#skF_3')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_323])).
% 3.96/2.01  tff(c_66, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.96/2.01  tff(c_328, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_327, c_66])).
% 3.96/2.01  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.96/2.01  tff(c_101, plain, (![A_59]: (v1_relat_1(A_59) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.96/2.01  tff(c_109, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_101])).
% 3.96/2.01  tff(c_119, plain, (![A_61]: (k6_relat_1(A_61)=k6_partfun1(A_61))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.96/2.01  tff(c_42, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/2.01  tff(c_125, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_119, c_42])).
% 3.96/2.01  tff(c_52, plain, (![A_45]: (k6_relat_1(A_45)=k6_partfun1(A_45))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.96/2.01  tff(c_46, plain, (![A_42]: (v1_funct_1(k6_relat_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.96/2.01  tff(c_70, plain, (![A_42]: (v1_funct_1(k6_partfun1(A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46])).
% 3.96/2.01  tff(c_137, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_125, c_70])).
% 3.96/2.01  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.96/2.01  tff(c_196, plain, (![A_75, B_76]: (r2_hidden('#skF_2'(A_75, B_76), A_75) | r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.96/2.01  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/2.01  tff(c_205, plain, (![A_75, B_76]: (~v1_xboole_0(A_75) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_196, c_2])).
% 3.96/2.01  tff(c_215, plain, (![B_83, A_84]: (v4_relat_1(B_83, A_84) | ~r1_tarski(k1_relat_1(B_83), A_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.96/2.01  tff(c_265, plain, (![B_90, B_91]: (v4_relat_1(B_90, B_91) | ~v1_relat_1(B_90) | ~v1_xboole_0(k1_relat_1(B_90)))), inference(resolution, [status(thm)], [c_205, c_215])).
% 3.96/2.01  tff(c_267, plain, (![B_91]: (v4_relat_1(k1_xboole_0, B_91) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_265])).
% 3.96/2.01  tff(c_269, plain, (![B_91]: (v4_relat_1(k1_xboole_0, B_91))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_109, c_267])).
% 3.96/2.01  tff(c_333, plain, (![B_104]: (v1_partfun1(B_104, k1_relat_1(B_104)) | ~v4_relat_1(B_104, k1_relat_1(B_104)) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.96/2.01  tff(c_343, plain, (v1_partfun1(k1_xboole_0, k1_relat_1(k1_xboole_0)) | ~v4_relat_1(k1_xboole_0, k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_333])).
% 3.96/2.01  tff(c_349, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_269, c_40, c_343])).
% 3.96/2.01  tff(c_178, plain, (![A_69, B_70]: (v1_yellow_1(k2_funcop_1(A_69, B_70)) | ~l1_orders_2(B_70))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.96/2.01  tff(c_181, plain, (![A_51]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_51))), inference(superposition, [status(thm), theory('equality')], [c_98, c_178])).
% 3.96/2.01  tff(c_191, plain, (![A_51]: (~l1_orders_2(A_51))), inference(splitLeft, [status(thm)], [c_181])).
% 3.96/2.01  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_68])).
% 3.96/2.01  tff(c_194, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_181])).
% 3.96/2.01  tff(c_641, plain, (![A_170]: (k5_yellow_1(k1_xboole_0, A_170)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_170) | ~v1_partfun1(A_170, k1_xboole_0) | ~v1_funct_1(A_170) | ~v4_relat_1(A_170, k1_xboole_0) | ~v1_relat_1(A_170))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.96/2.01  tff(c_644, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_269, c_641])).
% 3.96/2.01  tff(c_647, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_137, c_349, c_194, c_644])).
% 3.96/2.01  tff(c_649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_328, c_647])).
% 3.96/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/2.01  
% 3.96/2.01  Inference rules
% 3.96/2.01  ----------------------
% 3.96/2.01  #Ref     : 0
% 3.96/2.01  #Sup     : 126
% 3.96/2.01  #Fact    : 0
% 3.96/2.01  #Define  : 0
% 3.96/2.01  #Split   : 2
% 3.96/2.01  #Chain   : 0
% 3.96/2.01  #Close   : 0
% 3.96/2.01  
% 3.96/2.01  Ordering : KBO
% 3.96/2.01  
% 3.96/2.01  Simplification rules
% 3.96/2.01  ----------------------
% 3.96/2.01  #Subsume      : 29
% 3.96/2.01  #Demod        : 63
% 3.96/2.01  #Tautology    : 73
% 3.96/2.01  #SimpNegUnit  : 9
% 3.96/2.01  #BackRed      : 9
% 3.96/2.01  
% 3.96/2.01  #Partial instantiations: 0
% 3.96/2.01  #Strategies tried      : 1
% 3.96/2.01  
% 3.96/2.01  Timing (in seconds)
% 3.96/2.01  ----------------------
% 3.96/2.01  Preprocessing        : 0.61
% 3.96/2.01  Parsing              : 0.35
% 3.96/2.01  CNF conversion       : 0.04
% 3.96/2.01  Main loop            : 0.48
% 3.96/2.01  Inferencing          : 0.18
% 3.96/2.01  Reduction            : 0.15
% 3.96/2.01  Demodulation         : 0.11
% 3.96/2.01  BG Simplification    : 0.03
% 3.96/2.01  Subsumption          : 0.09
% 3.96/2.02  Abstraction          : 0.03
% 3.96/2.02  MUC search           : 0.00
% 3.96/2.02  Cooper               : 0.00
% 3.96/2.02  Total                : 1.15
% 3.96/2.02  Index Insertion      : 0.00
% 3.96/2.02  Index Deletion       : 0.00
% 3.96/2.02  Index Matching       : 0.00
% 3.96/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
