%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:57 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 134 expanded)
%              Number of leaves         :   26 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  113 ( 420 expanded)
%              Number of equality atoms :   11 (  27 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,A,B)
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                   => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [D_17,C_16,A_14,B_15] :
      ( r2_hidden(k1_funct_1(D_17,C_16),k2_relset_1(A_14,B_15,D_17))
      | k1_xboole_0 = B_15
      | ~ r2_hidden(C_16,A_14)
      | ~ m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(D_17,A_14,B_15)
      | ~ v1_funct_1(D_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_59,plain,(
    ! [A_46,B_47,C_48,D_49] :
      ( k3_funct_2(A_46,B_47,C_48,D_49) = k1_funct_1(C_48,D_49)
      | ~ m1_subset_1(D_49,A_46)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_2(C_48,A_46,B_47)
      | ~ v1_funct_1(C_48)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_65,plain,(
    ! [B_47,C_48] :
      ( k3_funct_2('#skF_1',B_47,C_48,'#skF_3') = k1_funct_1(C_48,'#skF_3')
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_47)))
      | ~ v1_funct_2(C_48,'#skF_1',B_47)
      | ~ v1_funct_1(C_48)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_59])).

tff(c_73,plain,(
    ! [B_50,C_51] :
      ( k3_funct_2('#skF_1',B_50,C_51,'#skF_3') = k1_funct_1(C_51,'#skF_3')
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_50)))
      | ~ v1_funct_2(C_51,'#skF_1',B_50)
      | ~ v1_funct_1(C_51) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_65])).

tff(c_76,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_73])).

tff(c_79,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_76])).

tff(c_14,plain,(
    ~ r2_hidden(k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_81,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_14])).

tff(c_98,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_81])).

tff(c_104,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_98])).

tff(c_106,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_109,plain,
    ( v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_106])).

tff(c_112,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_109])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_112])).

tff(c_115,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_130,plain,(
    ! [A_56] : r1_tarski('#skF_2',A_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_2])).

tff(c_29,plain,(
    ! [A_32,B_33] :
      ( r2_hidden(A_32,B_33)
      | v1_xboole_0(B_33)
      | ~ m1_subset_1(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( ~ r1_tarski(B_5,A_4)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_33,plain,(
    ! [B_33,A_32] :
      ( ~ r1_tarski(B_33,A_32)
      | v1_xboole_0(B_33)
      | ~ m1_subset_1(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_29,c_6])).

tff(c_133,plain,(
    ! [A_56] :
      ( v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_56,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_130,c_33])).

tff(c_136,plain,(
    ! [A_56] : ~ m1_subset_1(A_56,'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_133])).

tff(c_46,plain,(
    ! [A_37,B_38,C_39,D_40] :
      ( m1_subset_1(k3_funct_2(A_37,B_38,C_39,D_40),B_38)
      | ~ m1_subset_1(D_40,A_37)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38)))
      | ~ v1_funct_2(C_39,A_37,B_38)
      | ~ v1_funct_1(C_39)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    ! [D_40] :
      ( m1_subset_1(k3_funct_2('#skF_1','#skF_2','#skF_4',D_40),'#skF_2')
      | ~ m1_subset_1(D_40,'#skF_1')
      | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_46])).

tff(c_51,plain,(
    ! [D_40] :
      ( m1_subset_1(k3_funct_2('#skF_1','#skF_2','#skF_4',D_40),'#skF_2')
      | ~ m1_subset_1(D_40,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_48])).

tff(c_52,plain,(
    ! [D_40] :
      ( m1_subset_1(k3_funct_2('#skF_1','#skF_2','#skF_4',D_40),'#skF_2')
      | ~ m1_subset_1(D_40,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_51])).

tff(c_85,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_52])).

tff(c_89,plain,(
    m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_85])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.20  
% 2.11/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.20  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.11/1.20  
% 2.11/1.20  %Foreground sorts:
% 2.11/1.20  
% 2.11/1.20  
% 2.11/1.20  %Background operators:
% 2.11/1.20  
% 2.11/1.20  
% 2.11/1.20  %Foreground operators:
% 2.11/1.20  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.11/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.11/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.11/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.11/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.20  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.20  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.11/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.20  
% 2.11/1.22  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_funct_2)).
% 2.11/1.22  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.11/1.22  tff(f_76, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 2.11/1.22  tff(f_64, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.11/1.22  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.11/1.22  tff(f_38, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.11/1.22  tff(f_51, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 2.11/1.22  tff(c_24, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.11/1.22  tff(c_26, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.11/1.22  tff(c_22, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.11/1.22  tff(c_4, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.22  tff(c_20, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.11/1.22  tff(c_18, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.11/1.22  tff(c_16, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.11/1.22  tff(c_12, plain, (![D_17, C_16, A_14, B_15]: (r2_hidden(k1_funct_1(D_17, C_16), k2_relset_1(A_14, B_15, D_17)) | k1_xboole_0=B_15 | ~r2_hidden(C_16, A_14) | ~m1_subset_1(D_17, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_2(D_17, A_14, B_15) | ~v1_funct_1(D_17))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.11/1.22  tff(c_59, plain, (![A_46, B_47, C_48, D_49]: (k3_funct_2(A_46, B_47, C_48, D_49)=k1_funct_1(C_48, D_49) | ~m1_subset_1(D_49, A_46) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_2(C_48, A_46, B_47) | ~v1_funct_1(C_48) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.11/1.22  tff(c_65, plain, (![B_47, C_48]: (k3_funct_2('#skF_1', B_47, C_48, '#skF_3')=k1_funct_1(C_48, '#skF_3') | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_47))) | ~v1_funct_2(C_48, '#skF_1', B_47) | ~v1_funct_1(C_48) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_59])).
% 2.11/1.22  tff(c_73, plain, (![B_50, C_51]: (k3_funct_2('#skF_1', B_50, C_51, '#skF_3')=k1_funct_1(C_51, '#skF_3') | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_50))) | ~v1_funct_2(C_51, '#skF_1', B_50) | ~v1_funct_1(C_51))), inference(negUnitSimplification, [status(thm)], [c_26, c_65])).
% 2.11/1.22  tff(c_76, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_73])).
% 2.11/1.22  tff(c_79, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_76])).
% 2.11/1.22  tff(c_14, plain, (~r2_hidden(k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.11/1.22  tff(c_81, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_14])).
% 2.11/1.22  tff(c_98, plain, (k1_xboole_0='#skF_2' | ~r2_hidden('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_81])).
% 2.11/1.22  tff(c_104, plain, (k1_xboole_0='#skF_2' | ~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_98])).
% 2.11/1.22  tff(c_106, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_104])).
% 2.11/1.22  tff(c_109, plain, (v1_xboole_0('#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_4, c_106])).
% 2.11/1.22  tff(c_112, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_109])).
% 2.11/1.22  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_112])).
% 2.11/1.22  tff(c_115, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_104])).
% 2.11/1.22  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.22  tff(c_130, plain, (![A_56]: (r1_tarski('#skF_2', A_56))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_2])).
% 2.11/1.22  tff(c_29, plain, (![A_32, B_33]: (r2_hidden(A_32, B_33) | v1_xboole_0(B_33) | ~m1_subset_1(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.22  tff(c_6, plain, (![B_5, A_4]: (~r1_tarski(B_5, A_4) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.11/1.22  tff(c_33, plain, (![B_33, A_32]: (~r1_tarski(B_33, A_32) | v1_xboole_0(B_33) | ~m1_subset_1(A_32, B_33))), inference(resolution, [status(thm)], [c_29, c_6])).
% 2.11/1.22  tff(c_133, plain, (![A_56]: (v1_xboole_0('#skF_2') | ~m1_subset_1(A_56, '#skF_2'))), inference(resolution, [status(thm)], [c_130, c_33])).
% 2.11/1.22  tff(c_136, plain, (![A_56]: (~m1_subset_1(A_56, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_24, c_133])).
% 2.11/1.22  tff(c_46, plain, (![A_37, B_38, C_39, D_40]: (m1_subset_1(k3_funct_2(A_37, B_38, C_39, D_40), B_38) | ~m1_subset_1(D_40, A_37) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))) | ~v1_funct_2(C_39, A_37, B_38) | ~v1_funct_1(C_39) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.11/1.22  tff(c_48, plain, (![D_40]: (m1_subset_1(k3_funct_2('#skF_1', '#skF_2', '#skF_4', D_40), '#skF_2') | ~m1_subset_1(D_40, '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_46])).
% 2.11/1.22  tff(c_51, plain, (![D_40]: (m1_subset_1(k3_funct_2('#skF_1', '#skF_2', '#skF_4', D_40), '#skF_2') | ~m1_subset_1(D_40, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_48])).
% 2.11/1.22  tff(c_52, plain, (![D_40]: (m1_subset_1(k3_funct_2('#skF_1', '#skF_2', '#skF_4', D_40), '#skF_2') | ~m1_subset_1(D_40, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_26, c_51])).
% 2.11/1.22  tff(c_85, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_79, c_52])).
% 2.11/1.22  tff(c_89, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_85])).
% 2.11/1.22  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_89])).
% 2.11/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.22  
% 2.11/1.22  Inference rules
% 2.11/1.22  ----------------------
% 2.11/1.22  #Ref     : 0
% 2.11/1.22  #Sup     : 20
% 2.11/1.22  #Fact    : 0
% 2.11/1.22  #Define  : 0
% 2.11/1.22  #Split   : 3
% 2.11/1.22  #Chain   : 0
% 2.11/1.22  #Close   : 0
% 2.11/1.22  
% 2.11/1.22  Ordering : KBO
% 2.11/1.22  
% 2.11/1.22  Simplification rules
% 2.11/1.22  ----------------------
% 2.11/1.22  #Subsume      : 0
% 2.11/1.22  #Demod        : 15
% 2.11/1.22  #Tautology    : 4
% 2.11/1.22  #SimpNegUnit  : 8
% 2.11/1.22  #BackRed      : 8
% 2.11/1.22  
% 2.11/1.22  #Partial instantiations: 0
% 2.11/1.22  #Strategies tried      : 1
% 2.11/1.22  
% 2.11/1.22  Timing (in seconds)
% 2.11/1.22  ----------------------
% 2.11/1.22  Preprocessing        : 0.29
% 2.11/1.22  Parsing              : 0.16
% 2.11/1.22  CNF conversion       : 0.02
% 2.11/1.22  Main loop            : 0.16
% 2.11/1.22  Inferencing          : 0.06
% 2.11/1.22  Reduction            : 0.05
% 2.11/1.22  Demodulation         : 0.03
% 2.11/1.22  BG Simplification    : 0.01
% 2.11/1.22  Subsumption          : 0.02
% 2.11/1.22  Abstraction          : 0.01
% 2.11/1.22  MUC search           : 0.00
% 2.11/1.22  Cooper               : 0.00
% 2.11/1.22  Total                : 0.48
% 2.11/1.22  Index Insertion      : 0.00
% 2.11/1.22  Index Deletion       : 0.00
% 2.11/1.22  Index Matching       : 0.00
% 2.11/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
