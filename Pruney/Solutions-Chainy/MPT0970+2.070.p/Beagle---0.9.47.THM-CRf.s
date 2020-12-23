%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:29 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 179 expanded)
%              Number of leaves         :   35 (  76 expanded)
%              Depth                    :   10
%              Number of atoms          :  131 ( 440 expanded)
%              Number of equality atoms :   26 ( 116 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_426,plain,(
    ! [A_105,B_106,C_107] :
      ( k2_relset_1(A_105,B_106,C_107) = k2_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_441,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_426])).

tff(c_46,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_442,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_46])).

tff(c_508,plain,(
    ! [A_120,B_121,C_122] :
      ( m1_subset_1(k2_relset_1(A_120,B_121,C_122),k1_zfmisc_1(B_121))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_541,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_508])).

tff(c_556,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_541])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_560,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_556,c_20])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_564,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_560,c_8])).

tff(c_568,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_442,c_564])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_56,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_5'(D_34),'#skF_2')
      | ~ r2_hidden(D_34,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_54,plain,(
    ! [D_34] :
      ( k1_funct_1('#skF_4','#skF_5'(D_34)) = D_34
      | ~ r2_hidden(D_34,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_600,plain,(
    ! [D_124,C_125,A_126,B_127] :
      ( r2_hidden(k1_funct_1(D_124,C_125),k2_relset_1(A_126,B_127,D_124))
      | k1_xboole_0 = B_127
      | ~ r2_hidden(C_125,A_126)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_2(D_124,A_126,B_127)
      | ~ v1_funct_1(D_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_617,plain,(
    ! [D_34,A_126,B_127] :
      ( r2_hidden(D_34,k2_relset_1(A_126,B_127,'#skF_4'))
      | k1_xboole_0 = B_127
      | ~ r2_hidden('#skF_5'(D_34),A_126)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_2('#skF_4',A_126,B_127)
      | ~ v1_funct_1('#skF_4')
      | ~ r2_hidden(D_34,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_600])).

tff(c_691,plain,(
    ! [D_131,A_132,B_133] :
      ( r2_hidden(D_131,k2_relset_1(A_132,B_133,'#skF_4'))
      | k1_xboole_0 = B_133
      | ~ r2_hidden('#skF_5'(D_131),A_132)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ v1_funct_2('#skF_4',A_132,B_133)
      | ~ r2_hidden(D_131,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_617])).

tff(c_913,plain,(
    ! [D_155,B_156] :
      ( r2_hidden(D_155,k2_relset_1('#skF_2',B_156,'#skF_4'))
      | k1_xboole_0 = B_156
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_156)))
      | ~ v1_funct_2('#skF_4','#skF_2',B_156)
      | ~ r2_hidden(D_155,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_691])).

tff(c_918,plain,(
    ! [D_155] :
      ( r2_hidden(D_155,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ r2_hidden(D_155,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_913])).

tff(c_925,plain,(
    ! [D_155] :
      ( r2_hidden(D_155,k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(D_155,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_441,c_918])).

tff(c_927,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_925])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_155,plain,(
    ! [C_60,A_61,B_62] :
      ( v4_relat_1(C_60,A_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_187,plain,(
    ! [C_66,A_67] :
      ( v4_relat_1(C_66,A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_155])).

tff(c_191,plain,(
    ! [A_10,A_67] :
      ( v4_relat_1(A_10,A_67)
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_187])).

tff(c_74,plain,(
    ! [A_38,B_39] : v1_relat_1(k2_zfmisc_1(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_74])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_207,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(k1_relat_1(B_76),A_77)
      | ~ v4_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_216,plain,(
    ! [A_77] :
      ( r1_tarski(k1_xboole_0,A_77)
      | ~ v4_relat_1(k1_xboole_0,A_77)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_207])).

tff(c_221,plain,(
    ! [A_78] :
      ( r1_tarski(k1_xboole_0,A_78)
      | ~ v4_relat_1(k1_xboole_0,A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_216])).

tff(c_225,plain,(
    ! [A_67] :
      ( r1_tarski(k1_xboole_0,A_67)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_191,c_221])).

tff(c_228,plain,(
    ! [A_67] : r1_tarski(k1_xboole_0,A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_225])).

tff(c_948,plain,(
    ! [A_67] : r1_tarski('#skF_3',A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_228])).

tff(c_966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_948,c_568])).

tff(c_996,plain,(
    ! [D_160] :
      ( r2_hidden(D_160,k2_relat_1('#skF_4'))
      | ~ r2_hidden(D_160,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_925])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1145,plain,(
    ! [A_174] :
      ( r1_tarski(A_174,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_174,k2_relat_1('#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_996,c_4])).

tff(c_1153,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_1145])).

tff(c_1158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_568,c_568,c_1153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/2.06  
% 4.09/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/2.07  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.09/2.07  
% 4.09/2.07  %Foreground sorts:
% 4.09/2.07  
% 4.09/2.07  
% 4.09/2.07  %Background operators:
% 4.09/2.07  
% 4.09/2.07  
% 4.09/2.07  %Foreground operators:
% 4.09/2.07  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.09/2.07  tff('#skF_5', type, '#skF_5': $i > $i).
% 4.09/2.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.09/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.09/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.09/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/2.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.09/2.07  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.09/2.07  tff('#skF_2', type, '#skF_2': $i).
% 4.09/2.07  tff('#skF_3', type, '#skF_3': $i).
% 4.09/2.07  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.09/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.09/2.07  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.09/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/2.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.09/2.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.09/2.07  tff('#skF_4', type, '#skF_4': $i).
% 4.09/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/2.07  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.09/2.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.09/2.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.09/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.09/2.07  
% 4.09/2.09  tff(f_109, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 4.09/2.09  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.09/2.09  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.09/2.09  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.09/2.09  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.09/2.09  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.09/2.09  tff(f_90, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 4.09/2.09  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.09/2.09  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.09/2.09  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.09/2.09  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.09/2.09  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.09/2.09  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.09/2.09  tff(c_426, plain, (![A_105, B_106, C_107]: (k2_relset_1(A_105, B_106, C_107)=k2_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.09/2.09  tff(c_441, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_426])).
% 4.09/2.09  tff(c_46, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.09/2.09  tff(c_442, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_441, c_46])).
% 4.09/2.09  tff(c_508, plain, (![A_120, B_121, C_122]: (m1_subset_1(k2_relset_1(A_120, B_121, C_122), k1_zfmisc_1(B_121)) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.09/2.09  tff(c_541, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_441, c_508])).
% 4.09/2.09  tff(c_556, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_541])).
% 4.09/2.09  tff(c_20, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.09/2.09  tff(c_560, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_556, c_20])).
% 4.09/2.09  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.09/2.09  tff(c_564, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_560, c_8])).
% 4.09/2.09  tff(c_568, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_442, c_564])).
% 4.09/2.09  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.09/2.09  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.09/2.09  tff(c_56, plain, (![D_34]: (r2_hidden('#skF_5'(D_34), '#skF_2') | ~r2_hidden(D_34, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.09/2.09  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.09/2.09  tff(c_54, plain, (![D_34]: (k1_funct_1('#skF_4', '#skF_5'(D_34))=D_34 | ~r2_hidden(D_34, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.09/2.09  tff(c_600, plain, (![D_124, C_125, A_126, B_127]: (r2_hidden(k1_funct_1(D_124, C_125), k2_relset_1(A_126, B_127, D_124)) | k1_xboole_0=B_127 | ~r2_hidden(C_125, A_126) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_2(D_124, A_126, B_127) | ~v1_funct_1(D_124))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.09/2.09  tff(c_617, plain, (![D_34, A_126, B_127]: (r2_hidden(D_34, k2_relset_1(A_126, B_127, '#skF_4')) | k1_xboole_0=B_127 | ~r2_hidden('#skF_5'(D_34), A_126) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_2('#skF_4', A_126, B_127) | ~v1_funct_1('#skF_4') | ~r2_hidden(D_34, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_600])).
% 4.09/2.09  tff(c_691, plain, (![D_131, A_132, B_133]: (r2_hidden(D_131, k2_relset_1(A_132, B_133, '#skF_4')) | k1_xboole_0=B_133 | ~r2_hidden('#skF_5'(D_131), A_132) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~v1_funct_2('#skF_4', A_132, B_133) | ~r2_hidden(D_131, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_617])).
% 4.09/2.09  tff(c_913, plain, (![D_155, B_156]: (r2_hidden(D_155, k2_relset_1('#skF_2', B_156, '#skF_4')) | k1_xboole_0=B_156 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_156))) | ~v1_funct_2('#skF_4', '#skF_2', B_156) | ~r2_hidden(D_155, '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_691])).
% 4.09/2.09  tff(c_918, plain, (![D_155]: (r2_hidden(D_155, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~r2_hidden(D_155, '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_913])).
% 4.09/2.09  tff(c_925, plain, (![D_155]: (r2_hidden(D_155, k2_relat_1('#skF_4')) | k1_xboole_0='#skF_3' | ~r2_hidden(D_155, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_441, c_918])).
% 4.09/2.09  tff(c_927, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_925])).
% 4.09/2.09  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.09/2.09  tff(c_22, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.09/2.09  tff(c_16, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.09/2.09  tff(c_155, plain, (![C_60, A_61, B_62]: (v4_relat_1(C_60, A_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.09/2.09  tff(c_187, plain, (![C_66, A_67]: (v4_relat_1(C_66, A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_155])).
% 4.09/2.09  tff(c_191, plain, (![A_10, A_67]: (v4_relat_1(A_10, A_67) | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_187])).
% 4.09/2.09  tff(c_74, plain, (![A_38, B_39]: (v1_relat_1(k2_zfmisc_1(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.09/2.09  tff(c_76, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_74])).
% 4.09/2.09  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.09/2.09  tff(c_207, plain, (![B_76, A_77]: (r1_tarski(k1_relat_1(B_76), A_77) | ~v4_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.09/2.09  tff(c_216, plain, (![A_77]: (r1_tarski(k1_xboole_0, A_77) | ~v4_relat_1(k1_xboole_0, A_77) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_207])).
% 4.09/2.09  tff(c_221, plain, (![A_78]: (r1_tarski(k1_xboole_0, A_78) | ~v4_relat_1(k1_xboole_0, A_78))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_216])).
% 4.09/2.09  tff(c_225, plain, (![A_67]: (r1_tarski(k1_xboole_0, A_67) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_191, c_221])).
% 4.09/2.09  tff(c_228, plain, (![A_67]: (r1_tarski(k1_xboole_0, A_67))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_225])).
% 4.09/2.09  tff(c_948, plain, (![A_67]: (r1_tarski('#skF_3', A_67))), inference(demodulation, [status(thm), theory('equality')], [c_927, c_228])).
% 4.09/2.09  tff(c_966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_948, c_568])).
% 4.09/2.09  tff(c_996, plain, (![D_160]: (r2_hidden(D_160, k2_relat_1('#skF_4')) | ~r2_hidden(D_160, '#skF_3'))), inference(splitRight, [status(thm)], [c_925])).
% 4.09/2.09  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.09/2.09  tff(c_1145, plain, (![A_174]: (r1_tarski(A_174, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_174, k2_relat_1('#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_996, c_4])).
% 4.09/2.09  tff(c_1153, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_1145])).
% 4.09/2.09  tff(c_1158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_568, c_568, c_1153])).
% 4.09/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/2.09  
% 4.09/2.09  Inference rules
% 4.09/2.09  ----------------------
% 4.09/2.09  #Ref     : 0
% 4.09/2.09  #Sup     : 226
% 4.09/2.09  #Fact    : 0
% 4.09/2.09  #Define  : 0
% 4.09/2.09  #Split   : 5
% 4.09/2.09  #Chain   : 0
% 4.09/2.09  #Close   : 0
% 4.09/2.09  
% 4.09/2.09  Ordering : KBO
% 4.09/2.09  
% 4.09/2.09  Simplification rules
% 4.09/2.09  ----------------------
% 4.09/2.09  #Subsume      : 20
% 4.09/2.10  #Demod        : 183
% 4.09/2.10  #Tautology    : 89
% 4.09/2.10  #SimpNegUnit  : 3
% 4.09/2.10  #BackRed      : 33
% 4.09/2.10  
% 4.09/2.10  #Partial instantiations: 0
% 4.09/2.10  #Strategies tried      : 1
% 4.09/2.10  
% 4.09/2.10  Timing (in seconds)
% 4.09/2.10  ----------------------
% 4.09/2.10  Preprocessing        : 0.49
% 4.09/2.10  Parsing              : 0.25
% 4.09/2.10  CNF conversion       : 0.04
% 4.09/2.10  Main loop            : 0.69
% 4.09/2.10  Inferencing          : 0.24
% 4.09/2.10  Reduction            : 0.22
% 4.09/2.10  Demodulation         : 0.16
% 4.09/2.10  BG Simplification    : 0.03
% 4.09/2.10  Subsumption          : 0.14
% 4.09/2.10  Abstraction          : 0.03
% 4.09/2.10  MUC search           : 0.00
% 4.09/2.10  Cooper               : 0.00
% 4.09/2.10  Total                : 1.24
% 4.09/2.10  Index Insertion      : 0.00
% 4.09/2.10  Index Deletion       : 0.00
% 4.09/2.10  Index Matching       : 0.00
% 4.09/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
