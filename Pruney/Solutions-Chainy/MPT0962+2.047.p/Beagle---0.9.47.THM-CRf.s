%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:58 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 250 expanded)
%              Number of leaves         :   33 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  178 ( 568 expanded)
%              Number of equality atoms :   46 ( 117 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_55,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_10,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_49,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_67,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_71,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(resolution,[status(thm)],[c_49,c_67])).

tff(c_42,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1370,plain,(
    ! [C_244,A_245,B_246] :
      ( m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246)))
      | ~ r1_tarski(k2_relat_1(C_244),B_246)
      | ~ r1_tarski(k1_relat_1(C_244),A_245)
      | ~ v1_relat_1(C_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_79,plain,(
    ! [A_32] :
      ( k1_relat_1(A_32) = k1_xboole_0
      | k2_relat_1(A_32) != k1_xboole_0
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_83,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_79])).

tff(c_84,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_99,plain,(
    ! [C_36,B_37,A_38] :
      ( ~ v1_xboole_0(C_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(C_36))
      | ~ r2_hidden(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_117,plain,(
    ! [B_42,A_43,A_44] :
      ( ~ v1_xboole_0(B_42)
      | ~ r2_hidden(A_43,A_44)
      | ~ r1_tarski(A_44,B_42) ) ),
    inference(resolution,[status(thm)],[c_16,c_99])).

tff(c_121,plain,(
    ! [B_45,A_46] :
      ( ~ v1_xboole_0(B_45)
      | ~ r1_tarski(A_46,B_45)
      | k1_xboole_0 = A_46 ) ),
    inference(resolution,[status(thm)],[c_2,c_117])).

tff(c_127,plain,
    ( ~ v1_xboole_0('#skF_2')
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_121])).

tff(c_131,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_127])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40])).

tff(c_72,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_226,plain,(
    ! [C_70,A_71,B_72] :
      ( m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ r1_tarski(k2_relat_1(C_70),B_72)
      | ~ r1_tarski(k1_relat_1(C_70),A_71)
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_265,plain,(
    ! [C_75,A_76,B_77] :
      ( r1_tarski(C_75,k2_zfmisc_1(A_76,B_77))
      | ~ r1_tarski(k2_relat_1(C_75),B_77)
      | ~ r1_tarski(k1_relat_1(C_75),A_76)
      | ~ v1_relat_1(C_75) ) ),
    inference(resolution,[status(thm)],[c_226,c_14])).

tff(c_270,plain,(
    ! [A_76] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_76,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_76)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_265])).

tff(c_275,plain,(
    ! [A_78] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_78,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_270])).

tff(c_280,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_71,c_275])).

tff(c_138,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_147,plain,(
    ! [A_49,B_50,A_8] :
      ( k1_relset_1(A_49,B_50,A_8) = k1_relat_1(A_8)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_49,B_50)) ) ),
    inference(resolution,[status(thm)],[c_16,c_138])).

tff(c_287,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_147])).

tff(c_293,plain,(
    ! [B_79,C_80,A_81] :
      ( k1_xboole_0 = B_79
      | v1_funct_2(C_80,A_81,B_79)
      | k1_relset_1(A_81,B_79,C_80) != A_81
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_411,plain,(
    ! [B_99,A_100,A_101] :
      ( k1_xboole_0 = B_99
      | v1_funct_2(A_100,A_101,B_99)
      | k1_relset_1(A_101,B_99,A_100) != A_101
      | ~ r1_tarski(A_100,k2_zfmisc_1(A_101,B_99)) ) ),
    inference(resolution,[status(thm)],[c_16,c_293])).

tff(c_417,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_411])).

tff(c_425,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_417])).

tff(c_426,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_425])).

tff(c_4,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,(
    ! [B_33,A_34] :
      ( ~ r1_xboole_0(B_33,A_34)
      | ~ r1_tarski(B_33,A_34)
      | v1_xboole_0(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_88,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_85])).

tff(c_91,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_88])).

tff(c_452,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_91])).

tff(c_458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_452])).

tff(c_460,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_466,plain,(
    r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_42])).

tff(c_459,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_611,plain,(
    ! [C_139,A_140,B_141] :
      ( m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ r1_tarski(k2_relat_1(C_139),B_141)
      | ~ r1_tarski(k1_relat_1(C_139),A_140)
      | ~ v1_relat_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_650,plain,(
    ! [C_144,A_145,B_146] :
      ( r1_tarski(C_144,k2_zfmisc_1(A_145,B_146))
      | ~ r1_tarski(k2_relat_1(C_144),B_146)
      | ~ r1_tarski(k1_relat_1(C_144),A_145)
      | ~ v1_relat_1(C_144) ) ),
    inference(resolution,[status(thm)],[c_611,c_14])).

tff(c_652,plain,(
    ! [A_145,B_146] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_145,B_146))
      | ~ r1_tarski(k1_xboole_0,B_146)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_145)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_650])).

tff(c_659,plain,(
    ! [A_147,B_148] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_147,B_148))
      | ~ r1_tarski(k1_xboole_0,B_148)
      | ~ r1_tarski(k1_xboole_0,A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_459,c_652])).

tff(c_523,plain,(
    ! [A_118,B_119,C_120] :
      ( k1_relset_1(A_118,B_119,C_120) = k1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_532,plain,(
    ! [A_118,B_119,A_8] :
      ( k1_relset_1(A_118,B_119,A_8) = k1_relat_1(A_8)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_118,B_119)) ) ),
    inference(resolution,[status(thm)],[c_16,c_523])).

tff(c_674,plain,(
    ! [A_147,B_148] :
      ( k1_relset_1(A_147,B_148,'#skF_3') = k1_relat_1('#skF_3')
      | ~ r1_tarski(k1_xboole_0,B_148)
      | ~ r1_tarski(k1_xboole_0,A_147) ) ),
    inference(resolution,[status(thm)],[c_659,c_532])).

tff(c_1059,plain,(
    ! [A_192,B_193] :
      ( k1_relset_1(A_192,B_193,'#skF_3') = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_193)
      | ~ r1_tarski(k1_xboole_0,A_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_674])).

tff(c_1067,plain,(
    ! [A_194] :
      ( k1_relset_1(A_194,'#skF_2','#skF_3') = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_194) ) ),
    inference(resolution,[status(thm)],[c_466,c_1059])).

tff(c_1076,plain,(
    k1_relset_1(k1_xboole_0,'#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_1067])).

tff(c_562,plain,(
    ! [C_129,B_130] :
      ( v1_funct_2(C_129,k1_xboole_0,B_130)
      | k1_relset_1(k1_xboole_0,B_130,C_129) != k1_xboole_0
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_571,plain,(
    ! [A_8,B_130] :
      ( v1_funct_2(A_8,k1_xboole_0,B_130)
      | k1_relset_1(k1_xboole_0,B_130,A_8) != k1_xboole_0
      | ~ r1_tarski(A_8,k2_zfmisc_1(k1_xboole_0,B_130)) ) ),
    inference(resolution,[status(thm)],[c_16,c_562])).

tff(c_667,plain,(
    ! [B_148] :
      ( v1_funct_2('#skF_3',k1_xboole_0,B_148)
      | k1_relset_1(k1_xboole_0,B_148,'#skF_3') != k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_148)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_659,c_571])).

tff(c_1200,plain,(
    ! [B_203] :
      ( v1_funct_2('#skF_3',k1_xboole_0,B_203)
      | k1_relset_1(k1_xboole_0,B_203,'#skF_3') != k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_667])).

tff(c_461,plain,(
    ~ v1_funct_2('#skF_3',k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_72])).

tff(c_1207,plain,
    ( k1_relset_1(k1_xboole_0,'#skF_2','#skF_3') != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_1200,c_461])).

tff(c_1215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_1076,c_1207])).

tff(c_1216,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1394,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1370,c_1216])).

tff(c_1407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_71,c_42,c_1394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.61  
% 3.70/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.62  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.70/1.62  
% 3.70/1.62  %Foreground sorts:
% 3.70/1.62  
% 3.70/1.62  
% 3.70/1.62  %Background operators:
% 3.70/1.62  
% 3.70/1.62  
% 3.70/1.62  %Foreground operators:
% 3.70/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.70/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.70/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.70/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.70/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.70/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.70/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.70/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.70/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.70/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.62  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.70/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.70/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.70/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.62  
% 3.70/1.64  tff(f_117, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.70/1.64  tff(f_55, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.70/1.64  tff(f_57, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.70/1.64  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.70/1.64  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.70/1.64  tff(f_74, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.70/1.64  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.70/1.64  tff(f_68, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.70/1.64  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.70/1.64  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.70/1.64  tff(f_45, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.70/1.64  tff(f_53, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.70/1.64  tff(c_46, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.70/1.64  tff(c_10, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.70/1.64  tff(c_12, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.70/1.64  tff(c_49, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 3.70/1.64  tff(c_67, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.70/1.64  tff(c_71, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(resolution, [status(thm)], [c_49, c_67])).
% 3.70/1.64  tff(c_42, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.70/1.64  tff(c_1370, plain, (![C_244, A_245, B_246]: (m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))) | ~r1_tarski(k2_relat_1(C_244), B_246) | ~r1_tarski(k1_relat_1(C_244), A_245) | ~v1_relat_1(C_244))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.70/1.64  tff(c_79, plain, (![A_32]: (k1_relat_1(A_32)=k1_xboole_0 | k2_relat_1(A_32)!=k1_xboole_0 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.70/1.64  tff(c_83, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_79])).
% 3.70/1.64  tff(c_84, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_83])).
% 3.70/1.64  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.70/1.64  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.70/1.64  tff(c_99, plain, (![C_36, B_37, A_38]: (~v1_xboole_0(C_36) | ~m1_subset_1(B_37, k1_zfmisc_1(C_36)) | ~r2_hidden(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.70/1.64  tff(c_117, plain, (![B_42, A_43, A_44]: (~v1_xboole_0(B_42) | ~r2_hidden(A_43, A_44) | ~r1_tarski(A_44, B_42))), inference(resolution, [status(thm)], [c_16, c_99])).
% 3.70/1.64  tff(c_121, plain, (![B_45, A_46]: (~v1_xboole_0(B_45) | ~r1_tarski(A_46, B_45) | k1_xboole_0=A_46)), inference(resolution, [status(thm)], [c_2, c_117])).
% 3.70/1.64  tff(c_127, plain, (~v1_xboole_0('#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_121])).
% 3.70/1.64  tff(c_131, plain, (~v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_84, c_127])).
% 3.70/1.64  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.70/1.64  tff(c_40, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.70/1.64  tff(c_48, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40])).
% 3.70/1.64  tff(c_72, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 3.70/1.64  tff(c_226, plain, (![C_70, A_71, B_72]: (m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~r1_tarski(k2_relat_1(C_70), B_72) | ~r1_tarski(k1_relat_1(C_70), A_71) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.70/1.64  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.70/1.64  tff(c_265, plain, (![C_75, A_76, B_77]: (r1_tarski(C_75, k2_zfmisc_1(A_76, B_77)) | ~r1_tarski(k2_relat_1(C_75), B_77) | ~r1_tarski(k1_relat_1(C_75), A_76) | ~v1_relat_1(C_75))), inference(resolution, [status(thm)], [c_226, c_14])).
% 3.70/1.64  tff(c_270, plain, (![A_76]: (r1_tarski('#skF_3', k2_zfmisc_1(A_76, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_76) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_265])).
% 3.70/1.64  tff(c_275, plain, (![A_78]: (r1_tarski('#skF_3', k2_zfmisc_1(A_78, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_78))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_270])).
% 3.70/1.64  tff(c_280, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_71, c_275])).
% 3.70/1.64  tff(c_138, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.70/1.64  tff(c_147, plain, (![A_49, B_50, A_8]: (k1_relset_1(A_49, B_50, A_8)=k1_relat_1(A_8) | ~r1_tarski(A_8, k2_zfmisc_1(A_49, B_50)))), inference(resolution, [status(thm)], [c_16, c_138])).
% 3.70/1.64  tff(c_287, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_147])).
% 3.70/1.64  tff(c_293, plain, (![B_79, C_80, A_81]: (k1_xboole_0=B_79 | v1_funct_2(C_80, A_81, B_79) | k1_relset_1(A_81, B_79, C_80)!=A_81 | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_79))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.70/1.64  tff(c_411, plain, (![B_99, A_100, A_101]: (k1_xboole_0=B_99 | v1_funct_2(A_100, A_101, B_99) | k1_relset_1(A_101, B_99, A_100)!=A_101 | ~r1_tarski(A_100, k2_zfmisc_1(A_101, B_99)))), inference(resolution, [status(thm)], [c_16, c_293])).
% 3.70/1.64  tff(c_417, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_411])).
% 3.70/1.64  tff(c_425, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_417])).
% 3.70/1.64  tff(c_426, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_72, c_425])).
% 3.70/1.64  tff(c_4, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.70/1.64  tff(c_85, plain, (![B_33, A_34]: (~r1_xboole_0(B_33, A_34) | ~r1_tarski(B_33, A_34) | v1_xboole_0(B_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.70/1.64  tff(c_88, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_85])).
% 3.70/1.64  tff(c_91, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_88])).
% 3.70/1.64  tff(c_452, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_426, c_91])).
% 3.70/1.64  tff(c_458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_452])).
% 3.70/1.64  tff(c_460, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_83])).
% 3.70/1.64  tff(c_466, plain, (r1_tarski(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_460, c_42])).
% 3.70/1.64  tff(c_459, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_83])).
% 3.70/1.64  tff(c_611, plain, (![C_139, A_140, B_141]: (m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~r1_tarski(k2_relat_1(C_139), B_141) | ~r1_tarski(k1_relat_1(C_139), A_140) | ~v1_relat_1(C_139))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.70/1.64  tff(c_650, plain, (![C_144, A_145, B_146]: (r1_tarski(C_144, k2_zfmisc_1(A_145, B_146)) | ~r1_tarski(k2_relat_1(C_144), B_146) | ~r1_tarski(k1_relat_1(C_144), A_145) | ~v1_relat_1(C_144))), inference(resolution, [status(thm)], [c_611, c_14])).
% 3.70/1.64  tff(c_652, plain, (![A_145, B_146]: (r1_tarski('#skF_3', k2_zfmisc_1(A_145, B_146)) | ~r1_tarski(k1_xboole_0, B_146) | ~r1_tarski(k1_relat_1('#skF_3'), A_145) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_460, c_650])).
% 3.70/1.64  tff(c_659, plain, (![A_147, B_148]: (r1_tarski('#skF_3', k2_zfmisc_1(A_147, B_148)) | ~r1_tarski(k1_xboole_0, B_148) | ~r1_tarski(k1_xboole_0, A_147))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_459, c_652])).
% 3.70/1.64  tff(c_523, plain, (![A_118, B_119, C_120]: (k1_relset_1(A_118, B_119, C_120)=k1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.70/1.64  tff(c_532, plain, (![A_118, B_119, A_8]: (k1_relset_1(A_118, B_119, A_8)=k1_relat_1(A_8) | ~r1_tarski(A_8, k2_zfmisc_1(A_118, B_119)))), inference(resolution, [status(thm)], [c_16, c_523])).
% 3.70/1.64  tff(c_674, plain, (![A_147, B_148]: (k1_relset_1(A_147, B_148, '#skF_3')=k1_relat_1('#skF_3') | ~r1_tarski(k1_xboole_0, B_148) | ~r1_tarski(k1_xboole_0, A_147))), inference(resolution, [status(thm)], [c_659, c_532])).
% 3.70/1.64  tff(c_1059, plain, (![A_192, B_193]: (k1_relset_1(A_192, B_193, '#skF_3')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_193) | ~r1_tarski(k1_xboole_0, A_192))), inference(demodulation, [status(thm), theory('equality')], [c_459, c_674])).
% 3.70/1.64  tff(c_1067, plain, (![A_194]: (k1_relset_1(A_194, '#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_194))), inference(resolution, [status(thm)], [c_466, c_1059])).
% 3.70/1.64  tff(c_1076, plain, (k1_relset_1(k1_xboole_0, '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_71, c_1067])).
% 3.70/1.64  tff(c_562, plain, (![C_129, B_130]: (v1_funct_2(C_129, k1_xboole_0, B_130) | k1_relset_1(k1_xboole_0, B_130, C_129)!=k1_xboole_0 | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_130))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.70/1.64  tff(c_571, plain, (![A_8, B_130]: (v1_funct_2(A_8, k1_xboole_0, B_130) | k1_relset_1(k1_xboole_0, B_130, A_8)!=k1_xboole_0 | ~r1_tarski(A_8, k2_zfmisc_1(k1_xboole_0, B_130)))), inference(resolution, [status(thm)], [c_16, c_562])).
% 3.70/1.64  tff(c_667, plain, (![B_148]: (v1_funct_2('#skF_3', k1_xboole_0, B_148) | k1_relset_1(k1_xboole_0, B_148, '#skF_3')!=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_148) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_659, c_571])).
% 3.70/1.64  tff(c_1200, plain, (![B_203]: (v1_funct_2('#skF_3', k1_xboole_0, B_203) | k1_relset_1(k1_xboole_0, B_203, '#skF_3')!=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_203))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_667])).
% 3.70/1.64  tff(c_461, plain, (~v1_funct_2('#skF_3', k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_459, c_72])).
% 3.70/1.64  tff(c_1207, plain, (k1_relset_1(k1_xboole_0, '#skF_2', '#skF_3')!=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_1200, c_461])).
% 3.70/1.64  tff(c_1215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_466, c_1076, c_1207])).
% 3.70/1.64  tff(c_1216, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(splitRight, [status(thm)], [c_48])).
% 3.70/1.64  tff(c_1394, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1370, c_1216])).
% 3.70/1.64  tff(c_1407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_71, c_42, c_1394])).
% 3.70/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.64  
% 3.70/1.64  Inference rules
% 3.70/1.64  ----------------------
% 3.70/1.64  #Ref     : 0
% 3.70/1.64  #Sup     : 258
% 3.70/1.64  #Fact    : 0
% 3.70/1.64  #Define  : 0
% 3.70/1.64  #Split   : 7
% 3.70/1.64  #Chain   : 0
% 3.70/1.64  #Close   : 0
% 3.70/1.64  
% 3.70/1.64  Ordering : KBO
% 3.70/1.64  
% 3.70/1.64  Simplification rules
% 3.70/1.64  ----------------------
% 3.70/1.64  #Subsume      : 29
% 3.70/1.64  #Demod        : 240
% 3.70/1.64  #Tautology    : 77
% 3.70/1.64  #SimpNegUnit  : 8
% 3.70/1.64  #BackRed      : 55
% 3.70/1.64  
% 3.70/1.64  #Partial instantiations: 0
% 3.70/1.64  #Strategies tried      : 1
% 3.70/1.64  
% 3.70/1.64  Timing (in seconds)
% 3.70/1.64  ----------------------
% 3.70/1.64  Preprocessing        : 0.33
% 3.70/1.64  Parsing              : 0.17
% 3.70/1.64  CNF conversion       : 0.02
% 3.70/1.64  Main loop            : 0.55
% 3.70/1.64  Inferencing          : 0.21
% 3.70/1.64  Reduction            : 0.16
% 3.70/1.64  Demodulation         : 0.11
% 3.70/1.64  BG Simplification    : 0.03
% 3.70/1.64  Subsumption          : 0.11
% 3.70/1.64  Abstraction          : 0.03
% 3.70/1.64  MUC search           : 0.00
% 3.70/1.64  Cooper               : 0.00
% 3.70/1.64  Total                : 0.92
% 3.70/1.64  Index Insertion      : 0.00
% 3.70/1.64  Index Deletion       : 0.00
% 3.70/1.64  Index Matching       : 0.00
% 3.70/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
