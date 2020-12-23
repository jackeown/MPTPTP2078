%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:20 EST 2020

% Result     : Theorem 13.20s
% Output     : CNFRefutation 13.26s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 184 expanded)
%              Number of leaves         :   42 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  171 ( 510 expanded)
%              Number of equality atoms :   28 (  53 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(A))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(B))
                       => ( r1_tarski(k7_relset_1(A,B,C,D),E)
                        <=> r1_tarski(D,k8_relset_1(A,B,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(C,A)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | r1_tarski(C,k8_relset_1(A,B,D,k7_relset_1(A,B,D,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_28371,plain,(
    ! [A_764,B_765,C_766,D_767] :
      ( k8_relset_1(A_764,B_765,C_766,D_767) = k10_relat_1(C_766,D_767)
      | ~ m1_subset_1(C_766,k1_zfmisc_1(k2_zfmisc_1(A_764,B_765))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28378,plain,(
    ! [D_767] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_767) = k10_relat_1('#skF_3',D_767) ),
    inference(resolution,[status(thm)],[c_52,c_28371])).

tff(c_22,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_289,plain,(
    ! [B_98,A_99] :
      ( v1_relat_1(B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_99))
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_295,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_289])).

tff(c_305,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_295])).

tff(c_1071,plain,(
    ! [A_147,B_148,C_149,D_150] :
      ( k8_relset_1(A_147,B_148,C_149,D_150) = k10_relat_1(C_149,D_150)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1078,plain,(
    ! [D_150] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_150) = k10_relat_1('#skF_3',D_150) ),
    inference(resolution,[status(thm)],[c_52,c_1071])).

tff(c_68,plain,
    ( r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5')
    | r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_124,plain,(
    r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_1080,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1078,c_124])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_24,plain,(
    ! [C_20,A_18,B_19] :
      ( r1_tarski(k9_relat_1(C_20,A_18),k9_relat_1(C_20,B_19))
      | ~ r1_tarski(A_18,B_19)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_507,plain,(
    ! [B_114,A_115] :
      ( r1_tarski(k9_relat_1(B_114,k10_relat_1(B_114,A_115)),A_115)
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4140,plain,(
    ! [A_281,A_282,B_283] :
      ( r1_tarski(A_281,A_282)
      | ~ r1_tarski(A_281,k9_relat_1(B_283,k10_relat_1(B_283,A_282)))
      | ~ v1_funct_1(B_283)
      | ~ v1_relat_1(B_283) ) ),
    inference(resolution,[status(thm)],[c_507,c_14])).

tff(c_27195,plain,(
    ! [C_698,A_699,A_700] :
      ( r1_tarski(k9_relat_1(C_698,A_699),A_700)
      | ~ v1_funct_1(C_698)
      | ~ r1_tarski(A_699,k10_relat_1(C_698,A_700))
      | ~ v1_relat_1(C_698) ) ),
    inference(resolution,[status(thm)],[c_24,c_4140])).

tff(c_1255,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( k7_relset_1(A_155,B_156,C_157,D_158) = k9_relat_1(C_157,D_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1262,plain,(
    ! [D_158] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_158) = k9_relat_1('#skF_3',D_158) ),
    inference(resolution,[status(thm)],[c_52,c_1255])).

tff(c_62,plain,
    ( ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_199,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_62])).

tff(c_1263,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1262,c_199])).

tff(c_27337,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_27195,c_1263])).

tff(c_27421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_1080,c_56,c_27337])).

tff(c_27423,plain,(
    ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_28432,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28378,c_27423])).

tff(c_27620,plain,(
    ! [B_718,A_719] :
      ( v1_relat_1(B_718)
      | ~ m1_subset_1(B_718,k1_zfmisc_1(A_719))
      | ~ v1_relat_1(A_719) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_27626,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_27620])).

tff(c_27636,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_27626])).

tff(c_28250,plain,(
    ! [A_759,B_760,C_761,D_762] :
      ( k7_relset_1(A_759,B_760,C_761,D_762) = k9_relat_1(C_761,D_762)
      | ~ m1_subset_1(C_761,k1_zfmisc_1(k2_zfmisc_1(A_759,B_760))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28257,plain,(
    ! [D_762] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_762) = k9_relat_1('#skF_3',D_762) ),
    inference(resolution,[status(thm)],[c_52,c_28250])).

tff(c_27422,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_28260,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28257,c_27422])).

tff(c_28707,plain,(
    ! [A_783,C_784,B_785] :
      ( r1_tarski(A_783,k10_relat_1(C_784,B_785))
      | ~ r1_tarski(k9_relat_1(C_784,A_783),B_785)
      | ~ r1_tarski(A_783,k1_relat_1(C_784))
      | ~ v1_funct_1(C_784)
      | ~ v1_relat_1(C_784) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28728,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28260,c_28707])).

tff(c_28779,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27636,c_56,c_28728])).

tff(c_28780,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_28432,c_28779])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27877,plain,(
    ! [A_737,B_738,C_739] :
      ( k1_relset_1(A_737,B_738,C_739) = k1_relat_1(C_739)
      | ~ m1_subset_1(C_739,k1_zfmisc_1(k2_zfmisc_1(A_737,B_738))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_27886,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_27877])).

tff(c_29081,plain,(
    ! [B_797,A_798,C_799] :
      ( k8_relset_1(B_797,A_798,C_799,k7_relset_1(B_797,A_798,C_799,B_797)) = k1_relset_1(B_797,A_798,C_799)
      | ~ m1_subset_1(C_799,k1_zfmisc_1(k2_zfmisc_1(B_797,A_798))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_29086,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1')) = k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_29081])).

tff(c_29089,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28378,c_28257,c_27886,c_29086])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_29630,plain,(
    ! [B_817,C_818,A_819,D_820] :
      ( k1_xboole_0 = B_817
      | r1_tarski(C_818,k8_relset_1(A_819,B_817,D_820,k7_relset_1(A_819,B_817,D_820,C_818)))
      | ~ r1_tarski(C_818,A_819)
      | ~ m1_subset_1(D_820,k1_zfmisc_1(k2_zfmisc_1(A_819,B_817)))
      | ~ v1_funct_2(D_820,A_819,B_817)
      | ~ v1_funct_1(D_820) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_29676,plain,(
    ! [D_762] :
      ( k1_xboole_0 = '#skF_2'
      | r1_tarski(D_762,k8_relset_1('#skF_1','#skF_2','#skF_3',k9_relat_1('#skF_3',D_762)))
      | ~ r1_tarski(D_762,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28257,c_29630])).

tff(c_29692,plain,(
    ! [D_762] :
      ( k1_xboole_0 = '#skF_2'
      | r1_tarski(D_762,k10_relat_1('#skF_3',k9_relat_1('#skF_3',D_762)))
      | ~ r1_tarski(D_762,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_28378,c_29676])).

tff(c_36934,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_29692])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36940,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36934,c_2])).

tff(c_36942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_36940])).

tff(c_36945,plain,(
    ! [D_1065] :
      ( r1_tarski(D_1065,k10_relat_1('#skF_3',k9_relat_1('#skF_3',D_1065)))
      | ~ r1_tarski(D_1065,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_29692])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_72,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(A_76,B_77)
      | ~ m1_subset_1(A_76,k1_zfmisc_1(B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_84,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_72])).

tff(c_90,plain,(
    ! [A_80,B_81] :
      ( k2_xboole_0(A_80,B_81) = B_81
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_104,plain,(
    k2_xboole_0('#skF_4','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_84,c_90])).

tff(c_27428,plain,(
    ! [A_701,C_702,B_703] :
      ( r1_tarski(A_701,C_702)
      | ~ r1_tarski(k2_xboole_0(A_701,B_703),C_702) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_27434,plain,(
    ! [C_702] :
      ( r1_tarski('#skF_4',C_702)
      | ~ r1_tarski('#skF_1',C_702) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_27428])).

tff(c_37024,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')))
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_36945,c_27434])).

tff(c_37070,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_29089,c_37024])).

tff(c_37072,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28780,c_37070])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:41:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.20/6.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.20/6.30  
% 13.20/6.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.20/6.30  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.20/6.30  
% 13.20/6.30  %Foreground sorts:
% 13.20/6.30  
% 13.20/6.30  
% 13.20/6.30  %Background operators:
% 13.20/6.30  
% 13.20/6.30  
% 13.20/6.30  %Foreground operators:
% 13.20/6.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.20/6.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.20/6.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.20/6.30  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 13.20/6.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.20/6.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.20/6.30  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 13.20/6.30  tff('#skF_5', type, '#skF_5': $i).
% 13.20/6.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.20/6.30  tff('#skF_2', type, '#skF_2': $i).
% 13.20/6.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.20/6.30  tff('#skF_3', type, '#skF_3': $i).
% 13.20/6.30  tff('#skF_1', type, '#skF_1': $i).
% 13.20/6.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.20/6.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.20/6.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.20/6.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.20/6.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.20/6.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.20/6.30  tff('#skF_4', type, '#skF_4': $i).
% 13.20/6.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.20/6.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.20/6.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.20/6.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.20/6.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.20/6.30  
% 13.26/6.31  tff(f_145, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_2)).
% 13.26/6.31  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 13.26/6.31  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.26/6.31  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.26/6.31  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 13.26/6.31  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 13.26/6.31  tff(f_46, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 13.26/6.31  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 13.26/6.31  tff(f_81, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 13.26/6.31  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.26/6.31  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.26/6.31  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 13.26/6.31  tff(f_120, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r1_tarski(C, k8_relset_1(A, B, D, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_2)).
% 13.26/6.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 13.26/6.31  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.26/6.31  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 13.26/6.31  tff(f_36, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 13.26/6.31  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 13.26/6.31  tff(c_28371, plain, (![A_764, B_765, C_766, D_767]: (k8_relset_1(A_764, B_765, C_766, D_767)=k10_relat_1(C_766, D_767) | ~m1_subset_1(C_766, k1_zfmisc_1(k2_zfmisc_1(A_764, B_765))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.26/6.31  tff(c_28378, plain, (![D_767]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_767)=k10_relat_1('#skF_3', D_767))), inference(resolution, [status(thm)], [c_52, c_28371])).
% 13.26/6.31  tff(c_22, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.26/6.31  tff(c_289, plain, (![B_98, A_99]: (v1_relat_1(B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(A_99)) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.26/6.31  tff(c_295, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_289])).
% 13.26/6.31  tff(c_305, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_295])).
% 13.26/6.31  tff(c_1071, plain, (![A_147, B_148, C_149, D_150]: (k8_relset_1(A_147, B_148, C_149, D_150)=k10_relat_1(C_149, D_150) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.26/6.31  tff(c_1078, plain, (![D_150]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_150)=k10_relat_1('#skF_3', D_150))), inference(resolution, [status(thm)], [c_52, c_1071])).
% 13.26/6.31  tff(c_68, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5') | r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 13.26/6.31  tff(c_124, plain, (r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_68])).
% 13.26/6.31  tff(c_1080, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1078, c_124])).
% 13.26/6.31  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 13.26/6.31  tff(c_24, plain, (![C_20, A_18, B_19]: (r1_tarski(k9_relat_1(C_20, A_18), k9_relat_1(C_20, B_19)) | ~r1_tarski(A_18, B_19) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.26/6.31  tff(c_507, plain, (![B_114, A_115]: (r1_tarski(k9_relat_1(B_114, k10_relat_1(B_114, A_115)), A_115) | ~v1_funct_1(B_114) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.26/6.31  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.26/6.31  tff(c_4140, plain, (![A_281, A_282, B_283]: (r1_tarski(A_281, A_282) | ~r1_tarski(A_281, k9_relat_1(B_283, k10_relat_1(B_283, A_282))) | ~v1_funct_1(B_283) | ~v1_relat_1(B_283))), inference(resolution, [status(thm)], [c_507, c_14])).
% 13.26/6.31  tff(c_27195, plain, (![C_698, A_699, A_700]: (r1_tarski(k9_relat_1(C_698, A_699), A_700) | ~v1_funct_1(C_698) | ~r1_tarski(A_699, k10_relat_1(C_698, A_700)) | ~v1_relat_1(C_698))), inference(resolution, [status(thm)], [c_24, c_4140])).
% 13.26/6.31  tff(c_1255, plain, (![A_155, B_156, C_157, D_158]: (k7_relset_1(A_155, B_156, C_157, D_158)=k9_relat_1(C_157, D_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.26/6.31  tff(c_1262, plain, (![D_158]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_158)=k9_relat_1('#skF_3', D_158))), inference(resolution, [status(thm)], [c_52, c_1255])).
% 13.26/6.31  tff(c_62, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 13.26/6.31  tff(c_199, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_62])).
% 13.26/6.31  tff(c_1263, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1262, c_199])).
% 13.26/6.31  tff(c_27337, plain, (~v1_funct_1('#skF_3') | ~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_27195, c_1263])).
% 13.26/6.31  tff(c_27421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_305, c_1080, c_56, c_27337])).
% 13.26/6.31  tff(c_27423, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_68])).
% 13.26/6.31  tff(c_28432, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28378, c_27423])).
% 13.26/6.31  tff(c_27620, plain, (![B_718, A_719]: (v1_relat_1(B_718) | ~m1_subset_1(B_718, k1_zfmisc_1(A_719)) | ~v1_relat_1(A_719))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.26/6.31  tff(c_27626, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_27620])).
% 13.26/6.31  tff(c_27636, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_27626])).
% 13.26/6.31  tff(c_28250, plain, (![A_759, B_760, C_761, D_762]: (k7_relset_1(A_759, B_760, C_761, D_762)=k9_relat_1(C_761, D_762) | ~m1_subset_1(C_761, k1_zfmisc_1(k2_zfmisc_1(A_759, B_760))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.26/6.31  tff(c_28257, plain, (![D_762]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_762)=k9_relat_1('#skF_3', D_762))), inference(resolution, [status(thm)], [c_52, c_28250])).
% 13.26/6.31  tff(c_27422, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_68])).
% 13.26/6.31  tff(c_28260, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28257, c_27422])).
% 13.26/6.31  tff(c_28707, plain, (![A_783, C_784, B_785]: (r1_tarski(A_783, k10_relat_1(C_784, B_785)) | ~r1_tarski(k9_relat_1(C_784, A_783), B_785) | ~r1_tarski(A_783, k1_relat_1(C_784)) | ~v1_funct_1(C_784) | ~v1_relat_1(C_784))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.26/6.31  tff(c_28728, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28260, c_28707])).
% 13.26/6.31  tff(c_28779, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_27636, c_56, c_28728])).
% 13.26/6.31  tff(c_28780, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_28432, c_28779])).
% 13.26/6.32  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.26/6.32  tff(c_27877, plain, (![A_737, B_738, C_739]: (k1_relset_1(A_737, B_738, C_739)=k1_relat_1(C_739) | ~m1_subset_1(C_739, k1_zfmisc_1(k2_zfmisc_1(A_737, B_738))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.26/6.32  tff(c_27886, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_27877])).
% 13.26/6.32  tff(c_29081, plain, (![B_797, A_798, C_799]: (k8_relset_1(B_797, A_798, C_799, k7_relset_1(B_797, A_798, C_799, B_797))=k1_relset_1(B_797, A_798, C_799) | ~m1_subset_1(C_799, k1_zfmisc_1(k2_zfmisc_1(B_797, A_798))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.26/6.32  tff(c_29086, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_29081])).
% 13.26/6.32  tff(c_29089, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28378, c_28257, c_27886, c_29086])).
% 13.26/6.32  tff(c_58, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 13.26/6.32  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 13.26/6.32  tff(c_29630, plain, (![B_817, C_818, A_819, D_820]: (k1_xboole_0=B_817 | r1_tarski(C_818, k8_relset_1(A_819, B_817, D_820, k7_relset_1(A_819, B_817, D_820, C_818))) | ~r1_tarski(C_818, A_819) | ~m1_subset_1(D_820, k1_zfmisc_1(k2_zfmisc_1(A_819, B_817))) | ~v1_funct_2(D_820, A_819, B_817) | ~v1_funct_1(D_820))), inference(cnfTransformation, [status(thm)], [f_120])).
% 13.26/6.32  tff(c_29676, plain, (![D_762]: (k1_xboole_0='#skF_2' | r1_tarski(D_762, k8_relset_1('#skF_1', '#skF_2', '#skF_3', k9_relat_1('#skF_3', D_762))) | ~r1_tarski(D_762, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_28257, c_29630])).
% 13.26/6.32  tff(c_29692, plain, (![D_762]: (k1_xboole_0='#skF_2' | r1_tarski(D_762, k10_relat_1('#skF_3', k9_relat_1('#skF_3', D_762))) | ~r1_tarski(D_762, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_28378, c_29676])).
% 13.26/6.32  tff(c_36934, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_29692])).
% 13.26/6.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 13.26/6.32  tff(c_36940, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36934, c_2])).
% 13.26/6.32  tff(c_36942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_36940])).
% 13.26/6.32  tff(c_36945, plain, (![D_1065]: (r1_tarski(D_1065, k10_relat_1('#skF_3', k9_relat_1('#skF_3', D_1065))) | ~r1_tarski(D_1065, '#skF_1'))), inference(splitRight, [status(thm)], [c_29692])).
% 13.26/6.32  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 13.26/6.32  tff(c_72, plain, (![A_76, B_77]: (r1_tarski(A_76, B_77) | ~m1_subset_1(A_76, k1_zfmisc_1(B_77)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.26/6.32  tff(c_84, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_72])).
% 13.26/6.32  tff(c_90, plain, (![A_80, B_81]: (k2_xboole_0(A_80, B_81)=B_81 | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.26/6.32  tff(c_104, plain, (k2_xboole_0('#skF_4', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_84, c_90])).
% 13.26/6.32  tff(c_27428, plain, (![A_701, C_702, B_703]: (r1_tarski(A_701, C_702) | ~r1_tarski(k2_xboole_0(A_701, B_703), C_702))), inference(cnfTransformation, [status(thm)], [f_36])).
% 13.26/6.32  tff(c_27434, plain, (![C_702]: (r1_tarski('#skF_4', C_702) | ~r1_tarski('#skF_1', C_702))), inference(superposition, [status(thm), theory('equality')], [c_104, c_27428])).
% 13.26/6.32  tff(c_37024, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))) | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_36945, c_27434])).
% 13.26/6.32  tff(c_37070, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_29089, c_37024])).
% 13.26/6.32  tff(c_37072, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28780, c_37070])).
% 13.26/6.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.26/6.32  
% 13.26/6.32  Inference rules
% 13.26/6.32  ----------------------
% 13.26/6.32  #Ref     : 0
% 13.26/6.32  #Sup     : 9209
% 13.26/6.32  #Fact    : 0
% 13.26/6.32  #Define  : 0
% 13.26/6.32  #Split   : 82
% 13.26/6.32  #Chain   : 0
% 13.26/6.32  #Close   : 0
% 13.26/6.32  
% 13.26/6.32  Ordering : KBO
% 13.26/6.32  
% 13.26/6.32  Simplification rules
% 13.26/6.32  ----------------------
% 13.26/6.32  #Subsume      : 4473
% 13.26/6.32  #Demod        : 2457
% 13.26/6.32  #Tautology    : 1230
% 13.26/6.32  #SimpNegUnit  : 82
% 13.26/6.32  #BackRed      : 21
% 13.26/6.32  
% 13.26/6.32  #Partial instantiations: 0
% 13.26/6.32  #Strategies tried      : 1
% 13.26/6.32  
% 13.26/6.32  Timing (in seconds)
% 13.26/6.32  ----------------------
% 13.26/6.32  Preprocessing        : 0.37
% 13.26/6.32  Parsing              : 0.18
% 13.26/6.32  CNF conversion       : 0.03
% 13.26/6.32  Main loop            : 5.18
% 13.26/6.32  Inferencing          : 0.97
% 13.26/6.32  Reduction            : 2.18
% 13.26/6.32  Demodulation         : 1.61
% 13.26/6.32  BG Simplification    : 0.10
% 13.26/6.32  Subsumption          : 1.64
% 13.26/6.32  Abstraction          : 0.15
% 13.26/6.32  MUC search           : 0.00
% 13.26/6.32  Cooper               : 0.00
% 13.26/6.32  Total                : 5.58
% 13.26/6.32  Index Insertion      : 0.00
% 13.26/6.32  Index Deletion       : 0.00
% 13.26/6.32  Index Matching       : 0.00
% 13.26/6.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
