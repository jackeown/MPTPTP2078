%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:56 EST 2020

% Result     : Theorem 10.43s
% Output     : CNFRefutation 10.43s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 132 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   17
%              Number of atoms          :  136 ( 263 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( r1_tarski(k1_relat_1(D),B)
         => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(c_44,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,k1_zfmisc_1(B_30))
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,(
    ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_30])).

tff(c_20,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_70,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_76,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_70])).

tff(c_80,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_76])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_396,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k1_relat_1(A_78),k1_relat_1(B_79))
      | ~ r1_tarski(A_78,B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_32,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_113,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(B_42,C_41)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_127,plain,(
    ! [A_40] :
      ( r1_tarski(A_40,'#skF_2')
      | ~ r1_tarski(A_40,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_32,c_113])).

tff(c_402,plain,(
    ! [A_78] :
      ( r1_tarski(k1_relat_1(A_78),'#skF_2')
      | ~ r1_tarski(A_78,'#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_396,c_127])).

tff(c_413,plain,(
    ! [A_78] :
      ( r1_tarski(k1_relat_1(A_78),'#skF_2')
      | ~ r1_tarski(A_78,'#skF_4')
      | ~ v1_relat_1(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_402])).

tff(c_24,plain,(
    ! [A_18] :
      ( r1_tarski(A_18,k2_zfmisc_1(k1_relat_1(A_18),k2_relat_1(A_18)))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_247,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_tarski(k2_zfmisc_1(A_61,C_62),k2_zfmisc_1(B_63,C_62))
      | ~ r1_tarski(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_742,plain,(
    ! [A_106,B_107,C_108,A_109] :
      ( r1_tarski(A_106,k2_zfmisc_1(B_107,C_108))
      | ~ r1_tarski(A_106,k2_zfmisc_1(A_109,C_108))
      | ~ r1_tarski(A_109,B_107) ) ),
    inference(resolution,[status(thm)],[c_247,c_8])).

tff(c_773,plain,(
    ! [A_18,B_107] :
      ( r1_tarski(A_18,k2_zfmisc_1(B_107,k2_relat_1(A_18)))
      | ~ r1_tarski(k1_relat_1(A_18),B_107)
      | ~ v1_relat_1(A_18) ) ),
    inference(resolution,[status(thm)],[c_24,c_742])).

tff(c_39,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_43,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_39])).

tff(c_533,plain,(
    ! [A_89,A_90] :
      ( r1_tarski(A_89,k2_zfmisc_1(k1_relat_1(A_90),k2_relat_1(A_90)))
      | ~ r1_tarski(A_89,A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(resolution,[status(thm)],[c_24,c_113])).

tff(c_11848,plain,(
    ! [A_528,A_529,A_530] :
      ( r1_tarski(A_528,k2_zfmisc_1(k1_relat_1(A_529),k2_relat_1(A_529)))
      | ~ r1_tarski(A_528,A_530)
      | ~ r1_tarski(A_530,A_529)
      | ~ v1_relat_1(A_529) ) ),
    inference(resolution,[status(thm)],[c_533,c_8])).

tff(c_13894,plain,(
    ! [A_571] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1(A_571),k2_relat_1(A_571)))
      | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),A_571)
      | ~ v1_relat_1(A_571) ) ),
    inference(resolution,[status(thm)],[c_43,c_11848])).

tff(c_271,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(k2_relat_1(A_66),k2_relat_1(B_67))
      | ~ r1_tarski(A_66,B_67)
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_16,B_17)),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_126,plain,(
    ! [A_40,B_17,A_16] :
      ( r1_tarski(A_40,B_17)
      | ~ r1_tarski(A_40,k2_relat_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(resolution,[status(thm)],[c_22,c_113])).

tff(c_275,plain,(
    ! [A_66,B_17,A_16] :
      ( r1_tarski(k2_relat_1(A_66),B_17)
      | ~ r1_tarski(A_66,k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_271,c_126])).

tff(c_289,plain,(
    ! [A_66,B_17,A_16] :
      ( r1_tarski(k2_relat_1(A_66),B_17)
      | ~ r1_tarski(A_66,k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_275])).

tff(c_13948,plain,(
    ! [A_571] :
      ( r1_tarski(k2_relat_1('#skF_4'),k2_relat_1(A_571))
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),A_571)
      | ~ v1_relat_1(A_571) ) ),
    inference(resolution,[status(thm)],[c_13894,c_289])).

tff(c_16293,plain,(
    ! [A_613] :
      ( r1_tarski(k2_relat_1('#skF_4'),k2_relat_1(A_613))
      | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),A_613)
      | ~ v1_relat_1(A_613) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_13948])).

tff(c_16405,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1('#skF_4'),B_17)
      | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(k2_zfmisc_1(A_16,B_17)) ) ),
    inference(resolution,[status(thm)],[c_16293,c_126])).

tff(c_16701,plain,(
    ! [B_617,A_618] :
      ( r1_tarski(k2_relat_1('#skF_4'),B_617)
      | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1(A_618,B_617)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16405])).

tff(c_16793,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),k2_relat_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_16701])).

tff(c_16836,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k2_relat_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16793])).

tff(c_10,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(k2_zfmisc_1(C_8,A_6),k2_zfmisc_1(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_152,plain,(
    ! [C_45,A_46,B_47] :
      ( r1_tarski(k2_zfmisc_1(C_45,A_46),k2_zfmisc_1(C_45,B_47))
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_849,plain,(
    ! [A_116,C_117,B_118,A_119] :
      ( r1_tarski(A_116,k2_zfmisc_1(C_117,B_118))
      | ~ r1_tarski(A_116,k2_zfmisc_1(C_117,A_119))
      | ~ r1_tarski(A_119,B_118) ) ),
    inference(resolution,[status(thm)],[c_152,c_8])).

tff(c_4218,plain,(
    ! [C_309,A_310,B_311,B_312] :
      ( r1_tarski(k2_zfmisc_1(C_309,A_310),k2_zfmisc_1(C_309,B_311))
      | ~ r1_tarski(B_312,B_311)
      | ~ r1_tarski(A_310,B_312) ) ),
    inference(resolution,[status(thm)],[c_10,c_849])).

tff(c_4354,plain,(
    ! [C_309,A_310,B_17,A_16] :
      ( r1_tarski(k2_zfmisc_1(C_309,A_310),k2_zfmisc_1(C_309,B_17))
      | ~ r1_tarski(A_310,k2_relat_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(resolution,[status(thm)],[c_22,c_4218])).

tff(c_17093,plain,(
    ! [C_620] : r1_tarski(k2_zfmisc_1(C_620,k2_relat_1('#skF_4')),k2_zfmisc_1(C_620,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_16836,c_4354])).

tff(c_17672,plain,(
    ! [A_625,C_626] :
      ( r1_tarski(A_625,k2_zfmisc_1(C_626,'#skF_3'))
      | ~ r1_tarski(A_625,k2_zfmisc_1(C_626,k2_relat_1('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_17093,c_8])).

tff(c_17812,plain,(
    ! [B_107] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_107,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_107)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_773,c_17672])).

tff(c_18442,plain,(
    ! [B_629] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_629,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_629) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_17812])).

tff(c_18490,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_413,c_18442])).

tff(c_18525,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6,c_18490])).

tff(c_18527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_18525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.43/3.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.43/3.95  
% 10.43/3.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.43/3.96  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.43/3.96  
% 10.43/3.96  %Foreground sorts:
% 10.43/3.96  
% 10.43/3.96  
% 10.43/3.96  %Background operators:
% 10.43/3.96  
% 10.43/3.96  
% 10.43/3.96  %Foreground operators:
% 10.43/3.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.43/3.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.43/3.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.43/3.96  tff('#skF_2', type, '#skF_2': $i).
% 10.43/3.96  tff('#skF_3', type, '#skF_3': $i).
% 10.43/3.96  tff('#skF_1', type, '#skF_1': $i).
% 10.43/3.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.43/3.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.43/3.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.43/3.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.43/3.96  tff('#skF_4', type, '#skF_4': $i).
% 10.43/3.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.43/3.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.43/3.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.43/3.96  
% 10.43/3.97  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.43/3.97  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 10.43/3.97  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.43/3.97  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.43/3.97  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.43/3.97  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 10.43/3.97  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.43/3.97  tff(f_62, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 10.43/3.97  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 10.43/3.97  tff(f_58, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 10.43/3.97  tff(c_44, plain, (![A_29, B_30]: (m1_subset_1(A_29, k1_zfmisc_1(B_30)) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.43/3.97  tff(c_30, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.43/3.97  tff(c_52, plain, (~r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_30])).
% 10.43/3.97  tff(c_20, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.43/3.97  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.43/3.97  tff(c_70, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.43/3.97  tff(c_76, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_70])).
% 10.43/3.97  tff(c_80, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_76])).
% 10.43/3.97  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.43/3.97  tff(c_396, plain, (![A_78, B_79]: (r1_tarski(k1_relat_1(A_78), k1_relat_1(B_79)) | ~r1_tarski(A_78, B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.43/3.97  tff(c_32, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.43/3.97  tff(c_113, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(B_42, C_41) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.43/3.97  tff(c_127, plain, (![A_40]: (r1_tarski(A_40, '#skF_2') | ~r1_tarski(A_40, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_32, c_113])).
% 10.43/3.97  tff(c_402, plain, (![A_78]: (r1_tarski(k1_relat_1(A_78), '#skF_2') | ~r1_tarski(A_78, '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_396, c_127])).
% 10.43/3.97  tff(c_413, plain, (![A_78]: (r1_tarski(k1_relat_1(A_78), '#skF_2') | ~r1_tarski(A_78, '#skF_4') | ~v1_relat_1(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_402])).
% 10.43/3.97  tff(c_24, plain, (![A_18]: (r1_tarski(A_18, k2_zfmisc_1(k1_relat_1(A_18), k2_relat_1(A_18))) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.43/3.97  tff(c_247, plain, (![A_61, C_62, B_63]: (r1_tarski(k2_zfmisc_1(A_61, C_62), k2_zfmisc_1(B_63, C_62)) | ~r1_tarski(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.43/3.97  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.43/3.97  tff(c_742, plain, (![A_106, B_107, C_108, A_109]: (r1_tarski(A_106, k2_zfmisc_1(B_107, C_108)) | ~r1_tarski(A_106, k2_zfmisc_1(A_109, C_108)) | ~r1_tarski(A_109, B_107))), inference(resolution, [status(thm)], [c_247, c_8])).
% 10.43/3.97  tff(c_773, plain, (![A_18, B_107]: (r1_tarski(A_18, k2_zfmisc_1(B_107, k2_relat_1(A_18))) | ~r1_tarski(k1_relat_1(A_18), B_107) | ~v1_relat_1(A_18))), inference(resolution, [status(thm)], [c_24, c_742])).
% 10.43/3.97  tff(c_39, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.43/3.97  tff(c_43, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_39])).
% 10.43/3.97  tff(c_533, plain, (![A_89, A_90]: (r1_tarski(A_89, k2_zfmisc_1(k1_relat_1(A_90), k2_relat_1(A_90))) | ~r1_tarski(A_89, A_90) | ~v1_relat_1(A_90))), inference(resolution, [status(thm)], [c_24, c_113])).
% 10.43/3.97  tff(c_11848, plain, (![A_528, A_529, A_530]: (r1_tarski(A_528, k2_zfmisc_1(k1_relat_1(A_529), k2_relat_1(A_529))) | ~r1_tarski(A_528, A_530) | ~r1_tarski(A_530, A_529) | ~v1_relat_1(A_529))), inference(resolution, [status(thm)], [c_533, c_8])).
% 10.43/3.97  tff(c_13894, plain, (![A_571]: (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1(A_571), k2_relat_1(A_571))) | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), A_571) | ~v1_relat_1(A_571))), inference(resolution, [status(thm)], [c_43, c_11848])).
% 10.43/3.97  tff(c_271, plain, (![A_66, B_67]: (r1_tarski(k2_relat_1(A_66), k2_relat_1(B_67)) | ~r1_tarski(A_66, B_67) | ~v1_relat_1(B_67) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.43/3.97  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_16, B_17)), B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.43/3.97  tff(c_126, plain, (![A_40, B_17, A_16]: (r1_tarski(A_40, B_17) | ~r1_tarski(A_40, k2_relat_1(k2_zfmisc_1(A_16, B_17))))), inference(resolution, [status(thm)], [c_22, c_113])).
% 10.43/3.97  tff(c_275, plain, (![A_66, B_17, A_16]: (r1_tarski(k2_relat_1(A_66), B_17) | ~r1_tarski(A_66, k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_271, c_126])).
% 10.43/3.97  tff(c_289, plain, (![A_66, B_17, A_16]: (r1_tarski(k2_relat_1(A_66), B_17) | ~r1_tarski(A_66, k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_275])).
% 10.43/3.97  tff(c_13948, plain, (![A_571]: (r1_tarski(k2_relat_1('#skF_4'), k2_relat_1(A_571)) | ~v1_relat_1('#skF_4') | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), A_571) | ~v1_relat_1(A_571))), inference(resolution, [status(thm)], [c_13894, c_289])).
% 10.43/3.97  tff(c_16293, plain, (![A_613]: (r1_tarski(k2_relat_1('#skF_4'), k2_relat_1(A_613)) | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), A_613) | ~v1_relat_1(A_613))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_13948])).
% 10.43/3.97  tff(c_16405, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1('#skF_4'), B_17) | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(resolution, [status(thm)], [c_16293, c_126])).
% 10.43/3.97  tff(c_16701, plain, (![B_617, A_618]: (r1_tarski(k2_relat_1('#skF_4'), B_617) | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1(A_618, B_617)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16405])).
% 10.43/3.97  tff(c_16793, plain, (r1_tarski(k2_relat_1('#skF_4'), k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_16701])).
% 10.43/3.97  tff(c_16836, plain, (r1_tarski(k2_relat_1('#skF_4'), k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16793])).
% 10.43/3.97  tff(c_10, plain, (![C_8, A_6, B_7]: (r1_tarski(k2_zfmisc_1(C_8, A_6), k2_zfmisc_1(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.43/3.97  tff(c_152, plain, (![C_45, A_46, B_47]: (r1_tarski(k2_zfmisc_1(C_45, A_46), k2_zfmisc_1(C_45, B_47)) | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.43/3.97  tff(c_849, plain, (![A_116, C_117, B_118, A_119]: (r1_tarski(A_116, k2_zfmisc_1(C_117, B_118)) | ~r1_tarski(A_116, k2_zfmisc_1(C_117, A_119)) | ~r1_tarski(A_119, B_118))), inference(resolution, [status(thm)], [c_152, c_8])).
% 10.43/3.97  tff(c_4218, plain, (![C_309, A_310, B_311, B_312]: (r1_tarski(k2_zfmisc_1(C_309, A_310), k2_zfmisc_1(C_309, B_311)) | ~r1_tarski(B_312, B_311) | ~r1_tarski(A_310, B_312))), inference(resolution, [status(thm)], [c_10, c_849])).
% 10.43/3.97  tff(c_4354, plain, (![C_309, A_310, B_17, A_16]: (r1_tarski(k2_zfmisc_1(C_309, A_310), k2_zfmisc_1(C_309, B_17)) | ~r1_tarski(A_310, k2_relat_1(k2_zfmisc_1(A_16, B_17))))), inference(resolution, [status(thm)], [c_22, c_4218])).
% 10.43/3.97  tff(c_17093, plain, (![C_620]: (r1_tarski(k2_zfmisc_1(C_620, k2_relat_1('#skF_4')), k2_zfmisc_1(C_620, '#skF_3')))), inference(resolution, [status(thm)], [c_16836, c_4354])).
% 10.43/3.97  tff(c_17672, plain, (![A_625, C_626]: (r1_tarski(A_625, k2_zfmisc_1(C_626, '#skF_3')) | ~r1_tarski(A_625, k2_zfmisc_1(C_626, k2_relat_1('#skF_4'))))), inference(resolution, [status(thm)], [c_17093, c_8])).
% 10.43/3.97  tff(c_17812, plain, (![B_107]: (r1_tarski('#skF_4', k2_zfmisc_1(B_107, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), B_107) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_773, c_17672])).
% 10.43/3.97  tff(c_18442, plain, (![B_629]: (r1_tarski('#skF_4', k2_zfmisc_1(B_629, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), B_629))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_17812])).
% 10.43/3.97  tff(c_18490, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_413, c_18442])).
% 10.43/3.97  tff(c_18525, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_6, c_18490])).
% 10.43/3.97  tff(c_18527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_18525])).
% 10.43/3.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.43/3.97  
% 10.43/3.97  Inference rules
% 10.43/3.97  ----------------------
% 10.43/3.97  #Ref     : 0
% 10.43/3.97  #Sup     : 4128
% 10.43/3.97  #Fact    : 0
% 10.43/3.97  #Define  : 0
% 10.43/3.97  #Split   : 20
% 10.43/3.97  #Chain   : 0
% 10.43/3.97  #Close   : 0
% 10.43/3.97  
% 10.43/3.97  Ordering : KBO
% 10.43/3.97  
% 10.43/3.97  Simplification rules
% 10.43/3.97  ----------------------
% 10.43/3.97  #Subsume      : 1213
% 10.43/3.97  #Demod        : 1815
% 10.43/3.97  #Tautology    : 516
% 10.43/3.97  #SimpNegUnit  : 37
% 10.43/3.97  #BackRed      : 0
% 10.43/3.97  
% 10.43/3.97  #Partial instantiations: 0
% 10.43/3.97  #Strategies tried      : 1
% 10.43/3.97  
% 10.43/3.97  Timing (in seconds)
% 10.43/3.97  ----------------------
% 10.43/3.97  Preprocessing        : 0.29
% 10.43/3.97  Parsing              : 0.16
% 10.43/3.97  CNF conversion       : 0.02
% 10.43/3.97  Main loop            : 2.92
% 10.43/3.97  Inferencing          : 0.63
% 10.43/3.97  Reduction            : 0.95
% 10.43/3.97  Demodulation         : 0.68
% 10.43/3.97  BG Simplification    : 0.07
% 10.43/3.97  Subsumption          : 1.07
% 10.43/3.97  Abstraction          : 0.12
% 10.43/3.97  MUC search           : 0.00
% 10.43/3.97  Cooper               : 0.00
% 10.43/3.98  Total                : 3.24
% 10.43/3.98  Index Insertion      : 0.00
% 10.43/3.98  Index Deletion       : 0.00
% 10.43/3.98  Index Matching       : 0.00
% 10.43/3.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
