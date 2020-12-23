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
% DateTime   : Thu Dec  3 10:11:05 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   79 (  97 expanded)
%              Number of leaves         :   39 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  116 ( 189 expanded)
%              Number of equality atoms :   31 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k6_subset_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_43,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_96,plain,(
    ! [C_52,B_53,A_54] :
      ( v5_relat_1(C_52,B_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_54,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_105,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_96])).

tff(c_46,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_20,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_78,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_84,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_78])).

tff(c_88,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_84])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_141,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_150,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_141])).

tff(c_219,plain,(
    ! [B_102,A_103,C_104] :
      ( k1_xboole_0 = B_102
      | k1_relset_1(A_103,B_102,C_104) = A_103
      | ~ v1_funct_2(C_104,A_103,B_102)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_226,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_219])).

tff(c_231,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_150,c_226])).

tff(c_232,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_231])).

tff(c_22,plain,(
    ! [C_23,B_22,A_21] :
      ( m1_subset_1(k1_funct_1(C_23,B_22),A_21)
      | ~ r2_hidden(B_22,k1_relat_1(C_23))
      | ~ v1_funct_1(C_23)
      | ~ v5_relat_1(C_23,A_21)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_236,plain,(
    ! [B_22,A_21] :
      ( m1_subset_1(k1_funct_1('#skF_5',B_22),A_21)
      | ~ r2_hidden(B_22,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_21)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_22])).

tff(c_246,plain,(
    ! [B_105,A_106] :
      ( m1_subset_1(k1_funct_1('#skF_5',B_105),A_106)
      | ~ r2_hidden(B_105,'#skF_2')
      | ~ v5_relat_1('#skF_5',A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_52,c_236])).

tff(c_89,plain,(
    ! [A_48,B_49] :
      ( r2_hidden(A_48,B_49)
      | v1_xboole_0(B_49)
      | ~ m1_subset_1(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_93,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_89,c_42])).

tff(c_95,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_288,plain,
    ( ~ r2_hidden('#skF_4','#skF_2')
    | ~ v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_246,c_95])).

tff(c_306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_46,c_288])).

tff(c_307,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_9,B_10] : k6_subset_1(A_9,B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_7,B_8] : m1_subset_1(k6_subset_1(A_7,B_8),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_53,plain,(
    ! [A_7,B_8] : m1_subset_1(k4_xboole_0(A_7,B_8),k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10])).

tff(c_310,plain,(
    ! [C_109,B_110,A_111] :
      ( ~ v1_xboole_0(C_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(C_109))
      | ~ r2_hidden(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_317,plain,(
    ! [A_112,A_113,B_114] :
      ( ~ v1_xboole_0(A_112)
      | ~ r2_hidden(A_113,k4_xboole_0(A_112,B_114)) ) ),
    inference(resolution,[status(thm)],[c_53,c_310])).

tff(c_328,plain,(
    ! [A_115,B_116] :
      ( ~ v1_xboole_0(A_115)
      | k4_xboole_0(A_115,B_116) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_317])).

tff(c_332,plain,(
    ! [B_117] : k4_xboole_0('#skF_3',B_117) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_307,c_328])).

tff(c_68,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | k4_xboole_0(A_44,B_45) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_77,plain,(
    ! [A_44,B_6] :
      ( k1_xboole_0 = A_44
      | k4_xboole_0(A_44,k4_xboole_0(B_6,A_44)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_68,c_8])).

tff(c_344,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_77])).

tff(c_362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.30  
% 2.27/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.31  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k6_subset_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.27/1.31  
% 2.27/1.31  %Foreground sorts:
% 2.27/1.31  
% 2.27/1.31  
% 2.27/1.31  %Background operators:
% 2.27/1.31  
% 2.27/1.31  
% 2.27/1.31  %Foreground operators:
% 2.27/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.27/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.27/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.27/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.31  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.27/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.27/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.27/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.27/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.27/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.31  
% 2.27/1.32  tff(f_118, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.27/1.32  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.27/1.32  tff(f_67, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.27/1.32  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.27/1.32  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.27/1.32  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.27/1.32  tff(f_77, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 2.27/1.32  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.27/1.32  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.27/1.32  tff(f_45, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.27/1.32  tff(f_43, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.27/1.32  tff(f_58, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.27/1.32  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.27/1.32  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.27/1.32  tff(c_44, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.27/1.32  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.27/1.32  tff(c_96, plain, (![C_52, B_53, A_54]: (v5_relat_1(C_52, B_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_54, B_53))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.27/1.32  tff(c_105, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_96])).
% 2.27/1.32  tff(c_46, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.27/1.32  tff(c_20, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.27/1.32  tff(c_78, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.27/1.32  tff(c_84, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_78])).
% 2.27/1.32  tff(c_88, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_84])).
% 2.27/1.32  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.27/1.32  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.27/1.32  tff(c_141, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.27/1.32  tff(c_150, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_141])).
% 2.27/1.32  tff(c_219, plain, (![B_102, A_103, C_104]: (k1_xboole_0=B_102 | k1_relset_1(A_103, B_102, C_104)=A_103 | ~v1_funct_2(C_104, A_103, B_102) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.27/1.32  tff(c_226, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_219])).
% 2.27/1.32  tff(c_231, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_150, c_226])).
% 2.27/1.32  tff(c_232, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_231])).
% 2.27/1.32  tff(c_22, plain, (![C_23, B_22, A_21]: (m1_subset_1(k1_funct_1(C_23, B_22), A_21) | ~r2_hidden(B_22, k1_relat_1(C_23)) | ~v1_funct_1(C_23) | ~v5_relat_1(C_23, A_21) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.27/1.32  tff(c_236, plain, (![B_22, A_21]: (m1_subset_1(k1_funct_1('#skF_5', B_22), A_21) | ~r2_hidden(B_22, '#skF_2') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_21) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_232, c_22])).
% 2.27/1.32  tff(c_246, plain, (![B_105, A_106]: (m1_subset_1(k1_funct_1('#skF_5', B_105), A_106) | ~r2_hidden(B_105, '#skF_2') | ~v5_relat_1('#skF_5', A_106))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_52, c_236])).
% 2.27/1.32  tff(c_89, plain, (![A_48, B_49]: (r2_hidden(A_48, B_49) | v1_xboole_0(B_49) | ~m1_subset_1(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.27/1.32  tff(c_42, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.27/1.32  tff(c_93, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_89, c_42])).
% 2.27/1.32  tff(c_95, plain, (~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_93])).
% 2.27/1.32  tff(c_288, plain, (~r2_hidden('#skF_4', '#skF_2') | ~v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_246, c_95])).
% 2.27/1.32  tff(c_306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_46, c_288])).
% 2.27/1.32  tff(c_307, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_93])).
% 2.27/1.32  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.32  tff(c_12, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.32  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(k6_subset_1(A_7, B_8), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.27/1.32  tff(c_53, plain, (![A_7, B_8]: (m1_subset_1(k4_xboole_0(A_7, B_8), k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10])).
% 2.27/1.32  tff(c_310, plain, (![C_109, B_110, A_111]: (~v1_xboole_0(C_109) | ~m1_subset_1(B_110, k1_zfmisc_1(C_109)) | ~r2_hidden(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.27/1.32  tff(c_317, plain, (![A_112, A_113, B_114]: (~v1_xboole_0(A_112) | ~r2_hidden(A_113, k4_xboole_0(A_112, B_114)))), inference(resolution, [status(thm)], [c_53, c_310])).
% 2.27/1.32  tff(c_328, plain, (![A_115, B_116]: (~v1_xboole_0(A_115) | k4_xboole_0(A_115, B_116)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_317])).
% 2.27/1.32  tff(c_332, plain, (![B_117]: (k4_xboole_0('#skF_3', B_117)=k1_xboole_0)), inference(resolution, [status(thm)], [c_307, c_328])).
% 2.27/1.32  tff(c_68, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | k4_xboole_0(A_44, B_45)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.32  tff(c_8, plain, (![A_5, B_6]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k4_xboole_0(B_6, A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.27/1.32  tff(c_77, plain, (![A_44, B_6]: (k1_xboole_0=A_44 | k4_xboole_0(A_44, k4_xboole_0(B_6, A_44))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_8])).
% 2.27/1.32  tff(c_344, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_332, c_77])).
% 2.27/1.32  tff(c_362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_344])).
% 2.27/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.32  
% 2.27/1.32  Inference rules
% 2.27/1.32  ----------------------
% 2.27/1.32  #Ref     : 0
% 2.27/1.32  #Sup     : 62
% 2.27/1.32  #Fact    : 0
% 2.27/1.32  #Define  : 0
% 2.27/1.32  #Split   : 2
% 2.27/1.32  #Chain   : 0
% 2.27/1.32  #Close   : 0
% 2.27/1.32  
% 2.27/1.32  Ordering : KBO
% 2.27/1.32  
% 2.27/1.32  Simplification rules
% 2.27/1.32  ----------------------
% 2.27/1.32  #Subsume      : 0
% 2.27/1.32  #Demod        : 16
% 2.27/1.32  #Tautology    : 15
% 2.27/1.32  #SimpNegUnit  : 3
% 2.27/1.32  #BackRed      : 1
% 2.27/1.32  
% 2.27/1.32  #Partial instantiations: 0
% 2.27/1.32  #Strategies tried      : 1
% 2.27/1.32  
% 2.27/1.32  Timing (in seconds)
% 2.27/1.32  ----------------------
% 2.27/1.32  Preprocessing        : 0.33
% 2.27/1.32  Parsing              : 0.18
% 2.27/1.32  CNF conversion       : 0.02
% 2.27/1.32  Main loop            : 0.23
% 2.27/1.32  Inferencing          : 0.09
% 2.27/1.32  Reduction            : 0.07
% 2.27/1.32  Demodulation         : 0.05
% 2.27/1.32  BG Simplification    : 0.02
% 2.27/1.32  Subsumption          : 0.03
% 2.27/1.32  Abstraction          : 0.01
% 2.27/1.32  MUC search           : 0.00
% 2.27/1.32  Cooper               : 0.00
% 2.27/1.33  Total                : 0.59
% 2.27/1.33  Index Insertion      : 0.00
% 2.27/1.33  Index Deletion       : 0.00
% 2.27/1.33  Index Matching       : 0.00
% 2.27/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
