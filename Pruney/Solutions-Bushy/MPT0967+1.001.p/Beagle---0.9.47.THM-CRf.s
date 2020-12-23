%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0967+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:09 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.18s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 809 expanded)
%              Number of leaves         :   31 ( 260 expanded)
%              Depth                    :   19
%              Number of atoms          :  267 (2332 expanded)
%              Number of equality atoms :   67 ( 678 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_42,axiom,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_47,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_50,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_38,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | v1_xboole_0(B_18)
      | ~ m1_subset_1(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_81,plain,(
    ! [C_34,B_35,A_36] :
      ( ~ v1_xboole_0(C_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(C_34))
      | ~ r2_hidden(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_100,plain,(
    ! [B_39,A_40,A_41] :
      ( ~ v1_xboole_0(B_39)
      | ~ r2_hidden(A_40,A_41)
      | ~ r1_tarski(A_41,B_39) ) ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_104,plain,(
    ! [B_42,B_43,A_44] :
      ( ~ v1_xboole_0(B_42)
      | ~ r1_tarski(B_43,B_42)
      | v1_xboole_0(B_43)
      | ~ m1_subset_1(A_44,B_43) ) ),
    inference(resolution,[status(thm)],[c_24,c_100])).

tff(c_113,plain,(
    ! [A_44] :
      ( ~ v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_44,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_104])).

tff(c_114,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_34])).

tff(c_93,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_47,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_115,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_relset_1(A_45,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_128,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_115])).

tff(c_379,plain,(
    ! [B_82,A_83,C_84] :
      ( k1_xboole_0 = B_82
      | k1_relset_1(A_83,B_82,C_84) = A_83
      | ~ v1_funct_2(C_84,A_83,B_82)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_394,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_379])).

tff(c_404,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_128,c_394])).

tff(c_405,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_404])).

tff(c_197,plain,(
    ! [A_58,B_59,C_60] :
      ( m1_subset_1(k1_relset_1(A_58,B_59,C_60),k1_zfmisc_1(A_58))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_209,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_197])).

tff(c_214,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_209])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_221,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_214,c_26])).

tff(c_407,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_221])).

tff(c_506,plain,(
    ! [D_99,E_98,B_96,C_100,A_97] :
      ( m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(B_96,D_99)))
      | ~ r1_tarski(C_100,D_99)
      | ~ r1_tarski(A_97,B_96)
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_97,C_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_694,plain,(
    ! [E_118,B_119,A_120] :
      ( m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(B_119,'#skF_4')))
      | ~ r1_tarski(A_120,B_119)
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_120,'#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_506])).

tff(c_969,plain,(
    ! [E_134] :
      ( m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_407,c_694])).

tff(c_997,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_40,c_969])).

tff(c_20,plain,(
    ! [A_9,B_10,C_11] :
      ( k1_relset_1(A_9,B_10,C_11) = k1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1009,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_997,c_20])).

tff(c_1021,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_1009])).

tff(c_1023,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_997,c_26])).

tff(c_467,plain,(
    ! [B_87,C_88,A_89] :
      ( k1_xboole_0 = B_87
      | v1_funct_2(C_88,A_89,B_87)
      | k1_relset_1(A_89,B_87,C_88) != A_89
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_489,plain,(
    ! [B_87,A_19,A_89] :
      ( k1_xboole_0 = B_87
      | v1_funct_2(A_19,A_89,B_87)
      | k1_relset_1(A_89,B_87,A_19) != A_89
      | ~ r1_tarski(A_19,k2_zfmisc_1(A_89,B_87)) ) ),
    inference(resolution,[status(thm)],[c_28,c_467])).

tff(c_1043,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4')
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_1023,c_489])).

tff(c_1058,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1021,c_1043])).

tff(c_1059,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_1058])).

tff(c_16,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_49,plain,(
    ! [A_26] :
      ( k1_xboole_0 = A_26
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_53,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_49])).

tff(c_54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_16])).

tff(c_1090,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_54])).

tff(c_1095,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_1090])).

tff(c_1097,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_32,plain,(
    ! [A_24] :
      ( k1_xboole_0 = A_24
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1101,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1097,c_32])).

tff(c_1120,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_47])).

tff(c_18,plain,(
    ! [A_7] : m1_subset_1('#skF_1'(A_7),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1096,plain,(
    ! [A_44] :
      ( ~ m1_subset_1(A_44,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_1141,plain,(
    ! [A_139] : ~ m1_subset_1(A_139,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1096])).

tff(c_1146,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_1141])).

tff(c_1147,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1096])).

tff(c_1119,plain,(
    ! [A_24] :
      ( A_24 = '#skF_4'
      | ~ v1_xboole_0(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_32])).

tff(c_1150,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1147,c_1119])).

tff(c_1154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1120,c_1150])).

tff(c_1155,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1193,plain,(
    ! [A_152,B_153,C_154] :
      ( k1_relset_1(A_152,B_153,C_154) = k1_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1206,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1193])).

tff(c_1473,plain,(
    ! [B_187,A_188,C_189] :
      ( k1_xboole_0 = B_187
      | k1_relset_1(A_188,B_187,C_189) = A_188
      | ~ v1_funct_2(C_189,A_188,B_187)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_188,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1488,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1473])).

tff(c_1498,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1206,c_1488])).

tff(c_1499,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_1498])).

tff(c_1239,plain,(
    ! [A_157,B_158,C_159] :
      ( m1_subset_1(k1_relset_1(A_157,B_158,C_159),k1_zfmisc_1(A_157))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1251,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1206,c_1239])).

tff(c_1256,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1251])).

tff(c_1263,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1256,c_26])).

tff(c_1501,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1499,c_1263])).

tff(c_1680,plain,(
    ! [C_211,D_210,E_209,A_208,B_207] :
      ( m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(B_207,D_210)))
      | ~ r1_tarski(C_211,D_210)
      | ~ r1_tarski(A_208,B_207)
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(A_208,C_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1762,plain,(
    ! [E_221,B_222,A_223] :
      ( m1_subset_1(E_221,k1_zfmisc_1(k2_zfmisc_1(B_222,'#skF_4')))
      | ~ r1_tarski(A_223,B_222)
      | ~ m1_subset_1(E_221,k1_zfmisc_1(k2_zfmisc_1(A_223,'#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_1680])).

tff(c_1957,plain,(
    ! [E_232] :
      ( m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_1501,c_1762])).

tff(c_1976,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_40,c_1957])).

tff(c_1988,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1155,c_1976])).

tff(c_1990,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1989,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1995,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1990,c_1989])).

tff(c_2023,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_1995,c_46])).

tff(c_2024,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2023])).

tff(c_2006,plain,(
    ! [A_233] :
      ( A_233 = '#skF_3'
      | ~ v1_xboole_0(A_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1990,c_32])).

tff(c_2010,plain,(
    o_0_0_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16,c_2006])).

tff(c_2011,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_16])).

tff(c_2022,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_40])).

tff(c_2054,plain,(
    ! [A_245,B_246,C_247] :
      ( k1_relset_1(A_245,B_246,C_247) = k1_relat_1(C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2067,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2022,c_2054])).

tff(c_2122,plain,(
    ! [A_264,B_265,C_266] :
      ( m1_subset_1(k1_relset_1(A_264,B_265,C_266),k1_zfmisc_1(A_264))
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2134,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2067,c_2122])).

tff(c_2139,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2022,c_2134])).

tff(c_30,plain,(
    ! [C_23,B_22,A_21] :
      ( ~ v1_xboole_0(C_23)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(C_23))
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2141,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_21,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2139,c_30])).

tff(c_2149,plain,(
    ! [A_267] : ~ r2_hidden(A_267,k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2011,c_2141])).

tff(c_2154,plain,(
    ! [A_17] :
      ( v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_17,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_24,c_2149])).

tff(c_2258,plain,(
    ! [A_274] : ~ m1_subset_1(A_274,k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2154])).

tff(c_2263,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_2258])).

tff(c_2264,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2154])).

tff(c_2005,plain,(
    ! [A_24] :
      ( A_24 = '#skF_3'
      | ~ v1_xboole_0(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1990,c_32])).

tff(c_2268,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2264,c_2005])).

tff(c_2148,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2139,c_26])).

tff(c_2270,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2268,c_2148])).

tff(c_2520,plain,(
    ! [E_305,A_304,C_307,D_306,B_303] :
      ( m1_subset_1(E_305,k1_zfmisc_1(k2_zfmisc_1(B_303,D_306)))
      | ~ r1_tarski(C_307,D_306)
      | ~ r1_tarski(A_304,B_303)
      | ~ m1_subset_1(E_305,k1_zfmisc_1(k2_zfmisc_1(A_304,C_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2696,plain,(
    ! [E_327,B_328,A_329] :
      ( m1_subset_1(E_327,k1_zfmisc_1(k2_zfmisc_1(B_328,'#skF_4')))
      | ~ r1_tarski(A_329,B_328)
      | ~ m1_subset_1(E_327,k1_zfmisc_1(k2_zfmisc_1(A_329,'#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_2520])).

tff(c_3083,plain,(
    ! [E_344] :
      ( m1_subset_1(E_344,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ m1_subset_1(E_344,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_2270,c_2696])).

tff(c_3111,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_2022,c_3083])).

tff(c_3129,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3111,c_20])).

tff(c_3145,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2268,c_3129])).

tff(c_3147,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_3111,c_26])).

tff(c_6,plain,(
    ! [C_3,B_2] :
      ( v1_funct_2(C_3,k1_xboole_0,B_2)
      | k1_relset_1(k1_xboole_0,B_2,C_3) != k1_xboole_0
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2343,plain,(
    ! [C_281,B_282] :
      ( v1_funct_2(C_281,'#skF_3',B_282)
      | k1_relset_1('#skF_3',B_282,C_281) != '#skF_3'
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_282))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1990,c_1990,c_1990,c_1990,c_6])).

tff(c_2365,plain,(
    ! [A_19,B_282] :
      ( v1_funct_2(A_19,'#skF_3',B_282)
      | k1_relset_1('#skF_3',B_282,A_19) != '#skF_3'
      | ~ r1_tarski(A_19,k2_zfmisc_1('#skF_3',B_282)) ) ),
    inference(resolution,[status(thm)],[c_28,c_2343])).

tff(c_3170,plain,
    ( v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_3147,c_2365])).

tff(c_3187,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3145,c_3170])).

tff(c_3189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2024,c_3187])).

tff(c_3190,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_2023])).

tff(c_3231,plain,(
    ! [A_357,B_358,C_359] :
      ( k1_relset_1(A_357,B_358,C_359) = k1_relat_1(C_359)
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(A_357,B_358))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3244,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2022,c_3231])).

tff(c_3315,plain,(
    ! [A_375,B_376,C_377] :
      ( m1_subset_1(k1_relset_1(A_375,B_376,C_377),k1_zfmisc_1(A_375))
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3327,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3244,c_3315])).

tff(c_3332,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2022,c_3327])).

tff(c_3334,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_21,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3332,c_30])).

tff(c_3342,plain,(
    ! [A_378] : ~ r2_hidden(A_378,k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2011,c_3334])).

tff(c_3347,plain,(
    ! [A_17] :
      ( v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_17,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_24,c_3342])).

tff(c_3354,plain,(
    ! [A_379] : ~ m1_subset_1(A_379,k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3347])).

tff(c_3359,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_3354])).

tff(c_3360,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3347])).

tff(c_3364,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3360,c_2005])).

tff(c_3341,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_3332,c_26])).

tff(c_3366,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3364,c_3341])).

tff(c_3804,plain,(
    ! [D_427,B_424,C_428,A_425,E_426] :
      ( m1_subset_1(E_426,k1_zfmisc_1(k2_zfmisc_1(B_424,D_427)))
      | ~ r1_tarski(C_428,D_427)
      | ~ r1_tarski(A_425,B_424)
      | ~ m1_subset_1(E_426,k1_zfmisc_1(k2_zfmisc_1(A_425,C_428))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3877,plain,(
    ! [E_435,B_436,A_437] :
      ( m1_subset_1(E_435,k1_zfmisc_1(k2_zfmisc_1(B_436,'#skF_4')))
      | ~ r1_tarski(A_437,B_436)
      | ~ m1_subset_1(E_435,k1_zfmisc_1(k2_zfmisc_1(A_437,'#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_3804])).

tff(c_4261,plain,(
    ! [E_455] :
      ( m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_3366,c_3877])).

tff(c_4280,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_2022,c_4261])).

tff(c_4292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3190,c_4280])).

%------------------------------------------------------------------------------
