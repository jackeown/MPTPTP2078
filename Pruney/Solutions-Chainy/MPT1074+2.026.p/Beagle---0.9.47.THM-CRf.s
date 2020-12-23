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
% DateTime   : Thu Dec  3 10:18:10 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 122 expanded)
%              Number of leaves         :   25 (  57 expanded)
%              Depth                    :   18
%              Number of atoms          :  150 ( 388 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
          & ! [E] :
              ~ ( r2_hidden(E,A)
                & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_22,plain,(
    ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_63,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_1'(A_40,B_41),A_40)
      | r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [A_40] : r1_tarski(A_40,A_40) ),
    inference(resolution,[status(thm)],[c_63,c_4])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [C_42,B_43,A_44] :
      ( r2_hidden(C_42,B_43)
      | ~ r2_hidden(C_42,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_1,B_2,B_43] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_43)
      | ~ r1_tarski(A_1,B_43)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_30,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_137,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( r2_hidden('#skF_2'(A_61,B_62,C_63,D_64),A_61)
      | ~ r2_hidden(C_63,k2_relset_1(A_61,B_62,D_64))
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_2(D_64,A_61,B_62)
      | ~ v1_funct_1(D_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_148,plain,(
    ! [C_63] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_5',C_63,'#skF_6'),'#skF_4')
      | ~ r2_hidden(C_63,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_137])).

tff(c_155,plain,(
    ! [C_65] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_5',C_65,'#skF_6'),'#skF_4')
      | ~ r2_hidden(C_65,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_148])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_203,plain,(
    ! [C_76,B_77] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_5',C_76,'#skF_6'),B_77)
      | ~ r1_tarski('#skF_4',B_77)
      | ~ r2_hidden(C_76,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( m1_subset_1(B_7,A_6)
      | ~ r2_hidden(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_255,plain,(
    ! [C_85,B_86] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5',C_85,'#skF_6'),B_86)
      | v1_xboole_0(B_86)
      | ~ r1_tarski('#skF_4',B_86)
      | ~ r2_hidden(C_85,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_203,c_8])).

tff(c_273,plain,(
    ! [A_1,B_2,B_86] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_1'(A_1,B_2),'#skF_6'),B_86)
      | v1_xboole_0(B_86)
      | ~ r1_tarski('#skF_4',B_86)
      | ~ r1_tarski(A_1,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_80,c_255])).

tff(c_321,plain,(
    ! [D_96,A_97,B_98,C_99] :
      ( k1_funct_1(D_96,'#skF_2'(A_97,B_98,C_99,D_96)) = C_99
      | ~ r2_hidden(C_99,k2_relset_1(A_97,B_98,D_96))
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ v1_funct_2(D_96,A_97,B_98)
      | ~ v1_funct_1(D_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_602,plain,(
    ! [D_139,A_140,B_141,B_142] :
      ( k1_funct_1(D_139,'#skF_2'(A_140,B_141,'#skF_1'(k2_relset_1(A_140,B_141,D_139),B_142),D_139)) = '#skF_1'(k2_relset_1(A_140,B_141,D_139),B_142)
      | ~ m1_subset_1(D_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ v1_funct_2(D_139,A_140,B_141)
      | ~ v1_funct_1(D_139)
      | r1_tarski(k2_relset_1(A_140,B_141,D_139),B_142) ) ),
    inference(resolution,[status(thm)],[c_6,c_321])).

tff(c_160,plain,(
    ! [C_65] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5',C_65,'#skF_6'),'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ r2_hidden(C_65,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_155,c_8])).

tff(c_165,plain,(
    ! [C_66] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5',C_66,'#skF_6'),'#skF_4')
      | ~ r2_hidden(C_66,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_160])).

tff(c_183,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_1'(A_1,B_2),'#skF_6'),'#skF_4')
      | ~ r1_tarski(A_1,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_80,c_165])).

tff(c_227,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( k3_funct_2(A_81,B_82,C_83,D_84) = k1_funct_1(C_83,D_84)
      | ~ m1_subset_1(D_84,A_81)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ v1_funct_2(C_83,A_81,B_82)
      | ~ v1_funct_1(C_83)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_229,plain,(
    ! [B_82,C_83,A_1,B_2] :
      ( k3_funct_2('#skF_4',B_82,C_83,'#skF_2'('#skF_4','#skF_5','#skF_1'(A_1,B_2),'#skF_6')) = k1_funct_1(C_83,'#skF_2'('#skF_4','#skF_5','#skF_1'(A_1,B_2),'#skF_6'))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_82)))
      | ~ v1_funct_2(C_83,'#skF_4',B_82)
      | ~ v1_funct_1(C_83)
      | v1_xboole_0('#skF_4')
      | ~ r1_tarski(A_1,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_183,c_227])).

tff(c_281,plain,(
    ! [B_90,C_91,A_92,B_93] :
      ( k3_funct_2('#skF_4',B_90,C_91,'#skF_2'('#skF_4','#skF_5','#skF_1'(A_92,B_93),'#skF_6')) = k1_funct_1(C_91,'#skF_2'('#skF_4','#skF_5','#skF_1'(A_92,B_93),'#skF_6'))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_90)))
      | ~ v1_funct_2(C_91,'#skF_4',B_90)
      | ~ v1_funct_1(C_91)
      | ~ r1_tarski(A_92,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_92,B_93) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_229])).

tff(c_295,plain,(
    ! [A_92,B_93] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_92,B_93),'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_92,B_93),'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | ~ r1_tarski(A_92,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_26,c_281])).

tff(c_555,plain,(
    ! [A_126,B_127] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_126,B_127),'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_126,B_127),'#skF_6'))
      | ~ r1_tarski(A_126,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_126,B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_295])).

tff(c_24,plain,(
    ! [E_28] :
      ( r2_hidden(k3_funct_2('#skF_4','#skF_5','#skF_6',E_28),'#skF_3')
      | ~ m1_subset_1(E_28,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_571,plain,(
    ! [A_126,B_127] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_126,B_127),'#skF_6')),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_1'(A_126,B_127),'#skF_6'),'#skF_4')
      | ~ r1_tarski(A_126,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_126,B_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_24])).

tff(c_609,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_142),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_142),'#skF_6'),'#skF_4')
      | ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_142)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_571])).

tff(c_617,plain,(
    ! [B_143] :
      ( r2_hidden('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_143),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_143),'#skF_6'),'#skF_4')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_71,c_609])).

tff(c_621,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2),'#skF_3')
      | v1_xboole_0('#skF_4')
      | ~ r1_tarski('#skF_4','#skF_4')
      | ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2) ) ),
    inference(resolution,[status(thm)],[c_273,c_617])).

tff(c_638,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2),'#skF_3')
      | v1_xboole_0('#skF_4')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_71,c_621])).

tff(c_649,plain,(
    ! [B_144] :
      ( r2_hidden('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_144),'#skF_3')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_144) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_638])).

tff(c_655,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_649,c_4])).

tff(c_663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_22,c_655])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.56  
% 2.98/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.56  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.98/1.56  
% 2.98/1.56  %Foreground sorts:
% 2.98/1.56  
% 2.98/1.56  
% 2.98/1.56  %Background operators:
% 2.98/1.56  
% 2.98/1.56  
% 2.98/1.56  %Foreground operators:
% 2.98/1.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.98/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.98/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.56  tff('#skF_5', type, '#skF_5': $i).
% 2.98/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.98/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.98/1.56  tff('#skF_6', type, '#skF_6': $i).
% 2.98/1.56  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.98/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.98/1.56  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.98/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.98/1.56  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.98/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.56  
% 2.98/1.58  tff(f_95, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_funct_2)).
% 2.98/1.58  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.98/1.58  tff(f_73, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 2.98/1.58  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.98/1.58  tff(f_58, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.98/1.58  tff(c_22, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.98/1.58  tff(c_34, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.98/1.58  tff(c_63, plain, (![A_40, B_41]: (r2_hidden('#skF_1'(A_40, B_41), A_40) | r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.58  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.58  tff(c_71, plain, (![A_40]: (r1_tarski(A_40, A_40))), inference(resolution, [status(thm)], [c_63, c_4])).
% 2.98/1.58  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.58  tff(c_73, plain, (![C_42, B_43, A_44]: (r2_hidden(C_42, B_43) | ~r2_hidden(C_42, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.58  tff(c_80, plain, (![A_1, B_2, B_43]: (r2_hidden('#skF_1'(A_1, B_2), B_43) | ~r1_tarski(A_1, B_43) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_73])).
% 2.98/1.58  tff(c_30, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.98/1.58  tff(c_28, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.98/1.58  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.98/1.58  tff(c_137, plain, (![A_61, B_62, C_63, D_64]: (r2_hidden('#skF_2'(A_61, B_62, C_63, D_64), A_61) | ~r2_hidden(C_63, k2_relset_1(A_61, B_62, D_64)) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_2(D_64, A_61, B_62) | ~v1_funct_1(D_64))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.98/1.58  tff(c_148, plain, (![C_63]: (r2_hidden('#skF_2'('#skF_4', '#skF_5', C_63, '#skF_6'), '#skF_4') | ~r2_hidden(C_63, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_26, c_137])).
% 2.98/1.58  tff(c_155, plain, (![C_65]: (r2_hidden('#skF_2'('#skF_4', '#skF_5', C_65, '#skF_6'), '#skF_4') | ~r2_hidden(C_65, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_148])).
% 2.98/1.58  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.58  tff(c_203, plain, (![C_76, B_77]: (r2_hidden('#skF_2'('#skF_4', '#skF_5', C_76, '#skF_6'), B_77) | ~r1_tarski('#skF_4', B_77) | ~r2_hidden(C_76, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_155, c_2])).
% 2.98/1.58  tff(c_8, plain, (![B_7, A_6]: (m1_subset_1(B_7, A_6) | ~r2_hidden(B_7, A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.98/1.58  tff(c_255, plain, (![C_85, B_86]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', C_85, '#skF_6'), B_86) | v1_xboole_0(B_86) | ~r1_tarski('#skF_4', B_86) | ~r2_hidden(C_85, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_203, c_8])).
% 2.98/1.58  tff(c_273, plain, (![A_1, B_2, B_86]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1, B_2), '#skF_6'), B_86) | v1_xboole_0(B_86) | ~r1_tarski('#skF_4', B_86) | ~r1_tarski(A_1, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_80, c_255])).
% 2.98/1.58  tff(c_321, plain, (![D_96, A_97, B_98, C_99]: (k1_funct_1(D_96, '#skF_2'(A_97, B_98, C_99, D_96))=C_99 | ~r2_hidden(C_99, k2_relset_1(A_97, B_98, D_96)) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~v1_funct_2(D_96, A_97, B_98) | ~v1_funct_1(D_96))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.98/1.58  tff(c_602, plain, (![D_139, A_140, B_141, B_142]: (k1_funct_1(D_139, '#skF_2'(A_140, B_141, '#skF_1'(k2_relset_1(A_140, B_141, D_139), B_142), D_139))='#skF_1'(k2_relset_1(A_140, B_141, D_139), B_142) | ~m1_subset_1(D_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~v1_funct_2(D_139, A_140, B_141) | ~v1_funct_1(D_139) | r1_tarski(k2_relset_1(A_140, B_141, D_139), B_142))), inference(resolution, [status(thm)], [c_6, c_321])).
% 2.98/1.58  tff(c_160, plain, (![C_65]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', C_65, '#skF_6'), '#skF_4') | v1_xboole_0('#skF_4') | ~r2_hidden(C_65, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_155, c_8])).
% 2.98/1.58  tff(c_165, plain, (![C_66]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', C_66, '#skF_6'), '#skF_4') | ~r2_hidden(C_66, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_34, c_160])).
% 2.98/1.58  tff(c_183, plain, (![A_1, B_2]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1, B_2), '#skF_6'), '#skF_4') | ~r1_tarski(A_1, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_80, c_165])).
% 2.98/1.58  tff(c_227, plain, (![A_81, B_82, C_83, D_84]: (k3_funct_2(A_81, B_82, C_83, D_84)=k1_funct_1(C_83, D_84) | ~m1_subset_1(D_84, A_81) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~v1_funct_2(C_83, A_81, B_82) | ~v1_funct_1(C_83) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.98/1.58  tff(c_229, plain, (![B_82, C_83, A_1, B_2]: (k3_funct_2('#skF_4', B_82, C_83, '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1, B_2), '#skF_6'))=k1_funct_1(C_83, '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1, B_2), '#skF_6')) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_82))) | ~v1_funct_2(C_83, '#skF_4', B_82) | ~v1_funct_1(C_83) | v1_xboole_0('#skF_4') | ~r1_tarski(A_1, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_183, c_227])).
% 2.98/1.58  tff(c_281, plain, (![B_90, C_91, A_92, B_93]: (k3_funct_2('#skF_4', B_90, C_91, '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_92, B_93), '#skF_6'))=k1_funct_1(C_91, '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_92, B_93), '#skF_6')) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_90))) | ~v1_funct_2(C_91, '#skF_4', B_90) | ~v1_funct_1(C_91) | ~r1_tarski(A_92, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_92, B_93))), inference(negUnitSimplification, [status(thm)], [c_34, c_229])).
% 2.98/1.58  tff(c_295, plain, (![A_92, B_93]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_92, B_93), '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_92, B_93), '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | ~r1_tarski(A_92, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_26, c_281])).
% 2.98/1.58  tff(c_555, plain, (![A_126, B_127]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_126, B_127), '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_126, B_127), '#skF_6')) | ~r1_tarski(A_126, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_126, B_127))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_295])).
% 2.98/1.58  tff(c_24, plain, (![E_28]: (r2_hidden(k3_funct_2('#skF_4', '#skF_5', '#skF_6', E_28), '#skF_3') | ~m1_subset_1(E_28, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.98/1.58  tff(c_571, plain, (![A_126, B_127]: (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_126, B_127), '#skF_6')), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_126, B_127), '#skF_6'), '#skF_4') | ~r1_tarski(A_126, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_126, B_127))), inference(superposition, [status(thm), theory('equality')], [c_555, c_24])).
% 2.98/1.58  tff(c_609, plain, (![B_142]: (r2_hidden('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_142), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_142), '#skF_6'), '#skF_4') | ~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_142) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_142))), inference(superposition, [status(thm), theory('equality')], [c_602, c_571])).
% 2.98/1.58  tff(c_617, plain, (![B_143]: (r2_hidden('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_143), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_143), '#skF_6'), '#skF_4') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_143))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_71, c_609])).
% 2.98/1.58  tff(c_621, plain, (![B_2]: (r2_hidden('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2), '#skF_3') | v1_xboole_0('#skF_4') | ~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2))), inference(resolution, [status(thm)], [c_273, c_617])).
% 2.98/1.58  tff(c_638, plain, (![B_2]: (r2_hidden('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2), '#skF_3') | v1_xboole_0('#skF_4') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_71, c_621])).
% 2.98/1.58  tff(c_649, plain, (![B_144]: (r2_hidden('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_144), '#skF_3') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_144))), inference(negUnitSimplification, [status(thm)], [c_34, c_638])).
% 2.98/1.58  tff(c_655, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_649, c_4])).
% 2.98/1.58  tff(c_663, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_22, c_655])).
% 2.98/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.58  
% 2.98/1.58  Inference rules
% 2.98/1.58  ----------------------
% 2.98/1.58  #Ref     : 0
% 2.98/1.58  #Sup     : 136
% 2.98/1.58  #Fact    : 0
% 2.98/1.58  #Define  : 0
% 2.98/1.58  #Split   : 5
% 2.98/1.58  #Chain   : 0
% 2.98/1.58  #Close   : 0
% 2.98/1.58  
% 2.98/1.58  Ordering : KBO
% 2.98/1.58  
% 2.98/1.58  Simplification rules
% 2.98/1.58  ----------------------
% 2.98/1.58  #Subsume      : 15
% 2.98/1.58  #Demod        : 38
% 2.98/1.58  #Tautology    : 27
% 2.98/1.58  #SimpNegUnit  : 8
% 2.98/1.58  #BackRed      : 0
% 2.98/1.58  
% 2.98/1.58  #Partial instantiations: 0
% 2.98/1.58  #Strategies tried      : 1
% 2.98/1.58  
% 2.98/1.58  Timing (in seconds)
% 2.98/1.58  ----------------------
% 2.98/1.58  Preprocessing        : 0.32
% 2.98/1.58  Parsing              : 0.17
% 2.98/1.58  CNF conversion       : 0.02
% 2.98/1.58  Main loop            : 0.38
% 2.98/1.58  Inferencing          : 0.14
% 2.98/1.58  Reduction            : 0.10
% 2.98/1.58  Demodulation         : 0.07
% 2.98/1.58  BG Simplification    : 0.02
% 2.98/1.58  Subsumption          : 0.08
% 2.98/1.58  Abstraction          : 0.03
% 2.98/1.58  MUC search           : 0.00
% 2.98/1.58  Cooper               : 0.00
% 2.98/1.58  Total                : 0.73
% 2.98/1.58  Index Insertion      : 0.00
% 2.98/1.58  Index Deletion       : 0.00
% 2.98/1.58  Index Matching       : 0.00
% 2.98/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
