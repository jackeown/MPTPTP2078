%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1439+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:56 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 109 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :  192 ( 647 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r1_filter_1 > v2_struct_0 > v1_relat_1 > v10_lattices > l3_lattices > #nlpp > k8_filter_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_filter_1,type,(
    r1_filter_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k8_filter_1,type,(
    k8_filter_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v10_lattices(B)
              & l3_lattices(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & v10_lattices(C)
                  & l3_lattices(C) )
               => ( ( r1_filter_1(A,B)
                    & r1_filter_1(B,C) )
                 => r1_filter_1(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_filter_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => v1_relat_1(k8_filter_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_filter_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v10_lattices(B)
            & l3_lattices(B) )
         => ( r1_filter_1(A,B)
          <=> r4_wellord1(k8_filter_1(A),k8_filter_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_filter_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( ( r4_wellord1(A,B)
                  & r4_wellord1(B,C) )
               => r4_wellord1(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_wellord1)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10,plain,(
    ~ r1_filter_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_28,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_14,plain,(
    r1_filter_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6,plain,(
    ! [A_4] :
      ( v1_relat_1(k8_filter_1(A_4))
      | ~ l3_lattices(A_4)
      | ~ v10_lattices(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    r1_filter_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4,plain,(
    ! [A_1,B_3] :
      ( r4_wellord1(k8_filter_1(A_1),k8_filter_1(B_3))
      | ~ r1_filter_1(A_1,B_3)
      | ~ l3_lattices(B_3)
      | ~ v10_lattices(B_3)
      | v2_struct_0(B_3)
      | ~ l3_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_35,plain,(
    ! [A_20,B_21] :
      ( r4_wellord1(k8_filter_1(A_20),k8_filter_1(B_21))
      | ~ r1_filter_1(A_20,B_21)
      | ~ l3_lattices(B_21)
      | ~ v10_lattices(B_21)
      | v2_struct_0(B_21)
      | ~ l3_lattices(A_20)
      | ~ v10_lattices(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_5,C_11,B_9] :
      ( r4_wellord1(A_5,C_11)
      | ~ r4_wellord1(B_9,C_11)
      | ~ r4_wellord1(A_5,B_9)
      | ~ v1_relat_1(C_11)
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    ! [A_24,B_25,A_26] :
      ( r4_wellord1(A_24,k8_filter_1(B_25))
      | ~ r4_wellord1(A_24,k8_filter_1(A_26))
      | ~ v1_relat_1(k8_filter_1(B_25))
      | ~ v1_relat_1(k8_filter_1(A_26))
      | ~ v1_relat_1(A_24)
      | ~ r1_filter_1(A_26,B_25)
      | ~ l3_lattices(B_25)
      | ~ v10_lattices(B_25)
      | v2_struct_0(B_25)
      | ~ l3_lattices(A_26)
      | ~ v10_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(resolution,[status(thm)],[c_35,c_8])).

tff(c_48,plain,(
    ! [A_27,B_28,B_29] :
      ( r4_wellord1(k8_filter_1(A_27),k8_filter_1(B_28))
      | ~ v1_relat_1(k8_filter_1(B_28))
      | ~ v1_relat_1(k8_filter_1(B_29))
      | ~ v1_relat_1(k8_filter_1(A_27))
      | ~ r1_filter_1(B_29,B_28)
      | ~ l3_lattices(B_28)
      | ~ v10_lattices(B_28)
      | v2_struct_0(B_28)
      | ~ r1_filter_1(A_27,B_29)
      | ~ l3_lattices(B_29)
      | ~ v10_lattices(B_29)
      | v2_struct_0(B_29)
      | ~ l3_lattices(A_27)
      | ~ v10_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_4,c_44])).

tff(c_52,plain,(
    ! [A_30,B_31,A_32] :
      ( r4_wellord1(k8_filter_1(A_30),k8_filter_1(B_31))
      | ~ v1_relat_1(k8_filter_1(B_31))
      | ~ v1_relat_1(k8_filter_1(A_30))
      | ~ r1_filter_1(A_32,B_31)
      | ~ l3_lattices(B_31)
      | ~ v10_lattices(B_31)
      | v2_struct_0(B_31)
      | ~ r1_filter_1(A_30,A_32)
      | ~ l3_lattices(A_30)
      | ~ v10_lattices(A_30)
      | v2_struct_0(A_30)
      | ~ l3_lattices(A_32)
      | ~ v10_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_56,plain,(
    ! [A_30] :
      ( r4_wellord1(k8_filter_1(A_30),k8_filter_1('#skF_3'))
      | ~ v1_relat_1(k8_filter_1('#skF_3'))
      | ~ v1_relat_1(k8_filter_1(A_30))
      | ~ l3_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_filter_1(A_30,'#skF_2')
      | ~ l3_lattices(A_30)
      | ~ v10_lattices(A_30)
      | v2_struct_0(A_30)
      | ~ l3_lattices('#skF_2')
      | ~ v10_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_52])).

tff(c_63,plain,(
    ! [A_30] :
      ( r4_wellord1(k8_filter_1(A_30),k8_filter_1('#skF_3'))
      | ~ v1_relat_1(k8_filter_1('#skF_3'))
      | ~ v1_relat_1(k8_filter_1(A_30))
      | v2_struct_0('#skF_3')
      | ~ r1_filter_1(A_30,'#skF_2')
      | ~ l3_lattices(A_30)
      | ~ v10_lattices(A_30)
      | v2_struct_0(A_30)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_16,c_56])).

tff(c_64,plain,(
    ! [A_30] :
      ( r4_wellord1(k8_filter_1(A_30),k8_filter_1('#skF_3'))
      | ~ v1_relat_1(k8_filter_1('#skF_3'))
      | ~ v1_relat_1(k8_filter_1(A_30))
      | ~ r1_filter_1(A_30,'#skF_2')
      | ~ l3_lattices(A_30)
      | ~ v10_lattices(A_30)
      | v2_struct_0(A_30) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_20,c_63])).

tff(c_108,plain,(
    ~ v1_relat_1(k8_filter_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_111,plain,
    ( ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_114,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_111])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_114])).

tff(c_134,plain,(
    ! [A_36] :
      ( r4_wellord1(k8_filter_1(A_36),k8_filter_1('#skF_3'))
      | ~ v1_relat_1(k8_filter_1(A_36))
      | ~ r1_filter_1(A_36,'#skF_2')
      | ~ l3_lattices(A_36)
      | ~ v10_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( r1_filter_1(A_1,B_3)
      | ~ r4_wellord1(k8_filter_1(A_1),k8_filter_1(B_3))
      | ~ l3_lattices(B_3)
      | ~ v10_lattices(B_3)
      | v2_struct_0(B_3)
      | ~ l3_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_139,plain,(
    ! [A_36] :
      ( r1_filter_1(A_36,'#skF_3')
      | ~ l3_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v1_relat_1(k8_filter_1(A_36))
      | ~ r1_filter_1(A_36,'#skF_2')
      | ~ l3_lattices(A_36)
      | ~ v10_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_134,c_2])).

tff(c_148,plain,(
    ! [A_36] :
      ( r1_filter_1(A_36,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v1_relat_1(k8_filter_1(A_36))
      | ~ r1_filter_1(A_36,'#skF_2')
      | ~ l3_lattices(A_36)
      | ~ v10_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_139])).

tff(c_153,plain,(
    ! [A_37] :
      ( r1_filter_1(A_37,'#skF_3')
      | ~ v1_relat_1(k8_filter_1(A_37))
      | ~ r1_filter_1(A_37,'#skF_2')
      | ~ l3_lattices(A_37)
      | ~ v10_lattices(A_37)
      | v2_struct_0(A_37) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_148])).

tff(c_196,plain,(
    ! [A_40] :
      ( r1_filter_1(A_40,'#skF_3')
      | ~ r1_filter_1(A_40,'#skF_2')
      | ~ l3_lattices(A_40)
      | ~ v10_lattices(A_40)
      | v2_struct_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_6,c_153])).

tff(c_202,plain,
    ( r1_filter_1('#skF_1','#skF_3')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_196])).

tff(c_206,plain,
    ( r1_filter_1('#skF_1','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_202])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_10,c_206])).

%------------------------------------------------------------------------------
