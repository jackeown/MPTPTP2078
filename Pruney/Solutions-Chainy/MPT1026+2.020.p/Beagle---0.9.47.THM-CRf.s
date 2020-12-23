%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:41 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 334 expanded)
%              Number of leaves         :   29 ( 129 expanded)
%              Depth                    :   12
%              Number of atoms          :  175 ( 916 expanded)
%              Number of equality atoms :   16 ( 208 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_60,plain,(
    r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_137,plain,(
    ! [A_60,B_61,D_62] :
      ( '#skF_5'(A_60,B_61,k1_funct_2(A_60,B_61),D_62) = D_62
      | ~ r2_hidden(D_62,k1_funct_2(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_148,plain,(
    '#skF_5'('#skF_7','#skF_8',k1_funct_2('#skF_7','#skF_8'),'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_60,c_137])).

tff(c_20,plain,(
    ! [A_8,B_9,D_24] :
      ( v1_relat_1('#skF_5'(A_8,B_9,k1_funct_2(A_8,B_9),D_24))
      | ~ r2_hidden(D_24,k1_funct_2(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_155,plain,
    ( v1_relat_1('#skF_9')
    | ~ r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_20])).

tff(c_161,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_155])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_76,plain,(
    ~ v1_funct_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_94,plain,(
    ! [A_47,B_48,D_49] :
      ( '#skF_5'(A_47,B_48,k1_funct_2(A_47,B_48),D_49) = D_49
      | ~ r2_hidden(D_49,k1_funct_2(A_47,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_105,plain,(
    '#skF_5'('#skF_7','#skF_8',k1_funct_2('#skF_7','#skF_8'),'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_60,c_94])).

tff(c_18,plain,(
    ! [A_8,B_9,D_24] :
      ( v1_funct_1('#skF_5'(A_8,B_9,k1_funct_2(A_8,B_9),D_24))
      | ~ r2_hidden(D_24,k1_funct_2(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_109,plain,
    ( v1_funct_1('#skF_9')
    | ~ r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_18])).

tff(c_113,plain,(
    v1_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_109])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_113])).

tff(c_117,plain,(
    v1_funct_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_174,plain,(
    ! [A_67,B_68,D_69] :
      ( k1_relat_1('#skF_5'(A_67,B_68,k1_funct_2(A_67,B_68),D_69)) = A_67
      | ~ r2_hidden(D_69,k1_funct_2(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_186,plain,
    ( k1_relat_1('#skF_9') = '#skF_7'
    | ~ r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_174])).

tff(c_190,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_186])).

tff(c_556,plain,(
    ! [C_140,B_141] :
      ( r2_hidden('#skF_6'(k1_relat_1(C_140),B_141,C_140),k1_relat_1(C_140))
      | m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_140),B_141)))
      | ~ v1_funct_1(C_140)
      | ~ v1_relat_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_561,plain,(
    ! [B_141] :
      ( r2_hidden('#skF_6'('#skF_7',B_141,'#skF_9'),k1_relat_1('#skF_9'))
      | m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_9'),B_141)))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_556])).

tff(c_576,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_6'('#skF_7',B_142,'#skF_9'),'#skF_7')
      | m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_142))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_117,c_190,c_190,c_561])).

tff(c_116,plain,
    ( ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_125,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_580,plain,(
    r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_576,c_125])).

tff(c_254,plain,(
    ! [A_84,B_85,D_86] :
      ( r1_tarski(k2_relat_1('#skF_5'(A_84,B_85,k1_funct_2(A_84,B_85),D_86)),B_85)
      | ~ r2_hidden(D_86,k1_funct_2(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_262,plain,
    ( r1_tarski(k2_relat_1('#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_254])).

tff(c_266,plain,(
    r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_262])).

tff(c_163,plain,(
    ! [B_63,A_64] :
      ( r2_hidden(k1_funct_1(B_63,A_64),k2_relat_1(B_63))
      | ~ r2_hidden(A_64,k1_relat_1(B_63))
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_166,plain,(
    ! [B_63,A_64,B_2] :
      ( r2_hidden(k1_funct_1(B_63,A_64),B_2)
      | ~ r1_tarski(k2_relat_1(B_63),B_2)
      | ~ r2_hidden(A_64,k1_relat_1(B_63))
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_670,plain,(
    ! [C_154,B_155] :
      ( ~ r2_hidden(k1_funct_1(C_154,'#skF_6'(k1_relat_1(C_154),B_155,C_154)),B_155)
      | m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_154),B_155)))
      | ~ v1_funct_1(C_154)
      | ~ v1_relat_1(C_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_677,plain,(
    ! [B_155] :
      ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_6'('#skF_7',B_155,'#skF_9')),B_155)
      | m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_9'),B_155)))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_670])).

tff(c_689,plain,(
    ! [B_156] :
      ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_6'('#skF_7',B_156,'#skF_9')),B_156)
      | m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_156))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_117,c_190,c_677])).

tff(c_693,plain,(
    ! [B_2] :
      ( m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_2)))
      | ~ r1_tarski(k2_relat_1('#skF_9'),B_2)
      | ~ r2_hidden('#skF_6'('#skF_7',B_2,'#skF_9'),k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_166,c_689])).

tff(c_704,plain,(
    ! [B_157] :
      ( m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_157)))
      | ~ r1_tarski(k2_relat_1('#skF_9'),B_157)
      | ~ r2_hidden('#skF_6'('#skF_7',B_157,'#skF_9'),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_117,c_190,c_693])).

tff(c_707,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_704,c_125])).

tff(c_711,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_266,c_707])).

tff(c_712,plain,(
    ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_725,plain,(
    ! [A_167,B_168,D_169] :
      ( '#skF_5'(A_167,B_168,k1_funct_2(A_167,B_168),D_169) = D_169
      | ~ r2_hidden(D_169,k1_funct_2(A_167,B_168)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_736,plain,(
    '#skF_5'('#skF_7','#skF_8',k1_funct_2('#skF_7','#skF_8'),'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_60,c_725])).

tff(c_834,plain,(
    ! [A_188,B_189,D_190] :
      ( r1_tarski(k2_relat_1('#skF_5'(A_188,B_189,k1_funct_2(A_188,B_189),D_190)),B_189)
      | ~ r2_hidden(D_190,k1_funct_2(A_188,B_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_842,plain,
    ( r1_tarski(k2_relat_1('#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_834])).

tff(c_846,plain,(
    r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_842])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_34,B_35] :
      ( ~ r2_hidden('#skF_1'(A_34,B_35),B_35)
      | r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_743,plain,
    ( v1_relat_1('#skF_9')
    | ~ r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_20])).

tff(c_749,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_743])).

tff(c_751,plain,(
    ! [A_170,B_171,D_172] :
      ( k1_relat_1('#skF_5'(A_170,B_171,k1_funct_2(A_170,B_171),D_172)) = A_170
      | ~ r2_hidden(D_172,k1_funct_2(A_170,B_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_760,plain,
    ( k1_relat_1('#skF_9') = '#skF_7'
    | ~ r2_hidden('#skF_9',k1_funct_2('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_751])).

tff(c_764,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_760])).

tff(c_917,plain,(
    ! [C_208,B_209] :
      ( r2_hidden('#skF_6'(k1_relat_1(C_208),B_209,C_208),k1_relat_1(C_208))
      | v1_funct_2(C_208,k1_relat_1(C_208),B_209)
      | ~ v1_funct_1(C_208)
      | ~ v1_relat_1(C_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_922,plain,(
    ! [B_209] :
      ( r2_hidden('#skF_6'('#skF_7',B_209,'#skF_9'),k1_relat_1('#skF_9'))
      | v1_funct_2('#skF_9',k1_relat_1('#skF_9'),B_209)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_917])).

tff(c_937,plain,(
    ! [B_210] :
      ( r2_hidden('#skF_6'('#skF_7',B_210,'#skF_9'),'#skF_7')
      | v1_funct_2('#skF_9','#skF_7',B_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_117,c_764,c_764,c_922])).

tff(c_940,plain,(
    ! [B_210,B_2] :
      ( r2_hidden('#skF_6'('#skF_7',B_210,'#skF_9'),B_2)
      | ~ r1_tarski('#skF_7',B_2)
      | v1_funct_2('#skF_9','#skF_7',B_210) ) ),
    inference(resolution,[status(thm)],[c_937,c_2])).

tff(c_769,plain,(
    ! [B_173,A_174] :
      ( r2_hidden(k1_funct_1(B_173,A_174),k2_relat_1(B_173))
      | ~ r2_hidden(A_174,k1_relat_1(B_173))
      | ~ v1_funct_1(B_173)
      | ~ v1_relat_1(B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_772,plain,(
    ! [B_173,A_174,B_2] :
      ( r2_hidden(k1_funct_1(B_173,A_174),B_2)
      | ~ r1_tarski(k2_relat_1(B_173),B_2)
      | ~ r2_hidden(A_174,k1_relat_1(B_173))
      | ~ v1_funct_1(B_173)
      | ~ v1_relat_1(B_173) ) ),
    inference(resolution,[status(thm)],[c_769,c_2])).

tff(c_1022,plain,(
    ! [C_232,B_233] :
      ( ~ r2_hidden(k1_funct_1(C_232,'#skF_6'(k1_relat_1(C_232),B_233,C_232)),B_233)
      | v1_funct_2(C_232,k1_relat_1(C_232),B_233)
      | ~ v1_funct_1(C_232)
      | ~ v1_relat_1(C_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1033,plain,(
    ! [B_233] :
      ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_6'('#skF_7',B_233,'#skF_9')),B_233)
      | v1_funct_2('#skF_9',k1_relat_1('#skF_9'),B_233)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_1022])).

tff(c_1041,plain,(
    ! [B_234] :
      ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_6'('#skF_7',B_234,'#skF_9')),B_234)
      | v1_funct_2('#skF_9','#skF_7',B_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_117,c_764,c_1033])).

tff(c_1045,plain,(
    ! [B_2] :
      ( v1_funct_2('#skF_9','#skF_7',B_2)
      | ~ r1_tarski(k2_relat_1('#skF_9'),B_2)
      | ~ r2_hidden('#skF_6'('#skF_7',B_2,'#skF_9'),k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_772,c_1041])).

tff(c_1082,plain,(
    ! [B_237] :
      ( v1_funct_2('#skF_9','#skF_7',B_237)
      | ~ r1_tarski(k2_relat_1('#skF_9'),B_237)
      | ~ r2_hidden('#skF_6'('#skF_7',B_237,'#skF_9'),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_117,c_764,c_1045])).

tff(c_1086,plain,(
    ! [B_210] :
      ( ~ r1_tarski(k2_relat_1('#skF_9'),B_210)
      | ~ r1_tarski('#skF_7','#skF_7')
      | v1_funct_2('#skF_9','#skF_7',B_210) ) ),
    inference(resolution,[status(thm)],[c_940,c_1082])).

tff(c_1114,plain,(
    ! [B_240] :
      ( ~ r1_tarski(k2_relat_1('#skF_9'),B_240)
      | v1_funct_2('#skF_9','#skF_7',B_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_1086])).

tff(c_1117,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_846,c_1114])).

tff(c_1125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_712,c_1117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:50:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.60  
% 3.23/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.60  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 3.23/1.60  
% 3.23/1.60  %Foreground sorts:
% 3.23/1.60  
% 3.23/1.60  
% 3.23/1.60  %Background operators:
% 3.23/1.60  
% 3.23/1.60  
% 3.23/1.60  %Foreground operators:
% 3.23/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.23/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.60  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.23/1.60  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.23/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.23/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.23/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.23/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.23/1.60  tff('#skF_9', type, '#skF_9': $i).
% 3.23/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.60  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.23/1.60  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 3.23/1.60  tff('#skF_8', type, '#skF_8': $i).
% 3.23/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.60  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.23/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.23/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.23/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.23/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.23/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.60  
% 3.55/1.62  tff(f_82, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 3.55/1.62  tff(f_56, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 3.55/1.62  tff(f_73, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 3.55/1.62  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.55/1.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.55/1.62  tff(c_60, plain, (r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.55/1.62  tff(c_137, plain, (![A_60, B_61, D_62]: ('#skF_5'(A_60, B_61, k1_funct_2(A_60, B_61), D_62)=D_62 | ~r2_hidden(D_62, k1_funct_2(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.62  tff(c_148, plain, ('#skF_5'('#skF_7', '#skF_8', k1_funct_2('#skF_7', '#skF_8'), '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_60, c_137])).
% 3.55/1.62  tff(c_20, plain, (![A_8, B_9, D_24]: (v1_relat_1('#skF_5'(A_8, B_9, k1_funct_2(A_8, B_9), D_24)) | ~r2_hidden(D_24, k1_funct_2(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.62  tff(c_155, plain, (v1_relat_1('#skF_9') | ~r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_20])).
% 3.55/1.62  tff(c_161, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_155])).
% 3.55/1.62  tff(c_58, plain, (~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.55/1.62  tff(c_76, plain, (~v1_funct_1('#skF_9')), inference(splitLeft, [status(thm)], [c_58])).
% 3.55/1.62  tff(c_94, plain, (![A_47, B_48, D_49]: ('#skF_5'(A_47, B_48, k1_funct_2(A_47, B_48), D_49)=D_49 | ~r2_hidden(D_49, k1_funct_2(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.62  tff(c_105, plain, ('#skF_5'('#skF_7', '#skF_8', k1_funct_2('#skF_7', '#skF_8'), '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_60, c_94])).
% 3.55/1.62  tff(c_18, plain, (![A_8, B_9, D_24]: (v1_funct_1('#skF_5'(A_8, B_9, k1_funct_2(A_8, B_9), D_24)) | ~r2_hidden(D_24, k1_funct_2(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.62  tff(c_109, plain, (v1_funct_1('#skF_9') | ~r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_18])).
% 3.55/1.62  tff(c_113, plain, (v1_funct_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_109])).
% 3.55/1.62  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_113])).
% 3.55/1.62  tff(c_117, plain, (v1_funct_1('#skF_9')), inference(splitRight, [status(thm)], [c_58])).
% 3.55/1.62  tff(c_174, plain, (![A_67, B_68, D_69]: (k1_relat_1('#skF_5'(A_67, B_68, k1_funct_2(A_67, B_68), D_69))=A_67 | ~r2_hidden(D_69, k1_funct_2(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.62  tff(c_186, plain, (k1_relat_1('#skF_9')='#skF_7' | ~r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_174])).
% 3.55/1.62  tff(c_190, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_186])).
% 3.55/1.62  tff(c_556, plain, (![C_140, B_141]: (r2_hidden('#skF_6'(k1_relat_1(C_140), B_141, C_140), k1_relat_1(C_140)) | m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_140), B_141))) | ~v1_funct_1(C_140) | ~v1_relat_1(C_140))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.55/1.62  tff(c_561, plain, (![B_141]: (r2_hidden('#skF_6'('#skF_7', B_141, '#skF_9'), k1_relat_1('#skF_9')) | m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_9'), B_141))) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_190, c_556])).
% 3.55/1.62  tff(c_576, plain, (![B_142]: (r2_hidden('#skF_6'('#skF_7', B_142, '#skF_9'), '#skF_7') | m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_142))))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_117, c_190, c_190, c_561])).
% 3.55/1.62  tff(c_116, plain, (~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(splitRight, [status(thm)], [c_58])).
% 3.55/1.62  tff(c_125, plain, (~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(splitLeft, [status(thm)], [c_116])).
% 3.55/1.62  tff(c_580, plain, (r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_7')), inference(resolution, [status(thm)], [c_576, c_125])).
% 3.55/1.62  tff(c_254, plain, (![A_84, B_85, D_86]: (r1_tarski(k2_relat_1('#skF_5'(A_84, B_85, k1_funct_2(A_84, B_85), D_86)), B_85) | ~r2_hidden(D_86, k1_funct_2(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.62  tff(c_262, plain, (r1_tarski(k2_relat_1('#skF_9'), '#skF_8') | ~r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_254])).
% 3.55/1.62  tff(c_266, plain, (r1_tarski(k2_relat_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_262])).
% 3.55/1.62  tff(c_163, plain, (![B_63, A_64]: (r2_hidden(k1_funct_1(B_63, A_64), k2_relat_1(B_63)) | ~r2_hidden(A_64, k1_relat_1(B_63)) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.55/1.62  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.62  tff(c_166, plain, (![B_63, A_64, B_2]: (r2_hidden(k1_funct_1(B_63, A_64), B_2) | ~r1_tarski(k2_relat_1(B_63), B_2) | ~r2_hidden(A_64, k1_relat_1(B_63)) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_163, c_2])).
% 3.55/1.62  tff(c_670, plain, (![C_154, B_155]: (~r2_hidden(k1_funct_1(C_154, '#skF_6'(k1_relat_1(C_154), B_155, C_154)), B_155) | m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_154), B_155))) | ~v1_funct_1(C_154) | ~v1_relat_1(C_154))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.55/1.62  tff(c_677, plain, (![B_155]: (~r2_hidden(k1_funct_1('#skF_9', '#skF_6'('#skF_7', B_155, '#skF_9')), B_155) | m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_9'), B_155))) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_190, c_670])).
% 3.55/1.62  tff(c_689, plain, (![B_156]: (~r2_hidden(k1_funct_1('#skF_9', '#skF_6'('#skF_7', B_156, '#skF_9')), B_156) | m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_156))))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_117, c_190, c_677])).
% 3.55/1.62  tff(c_693, plain, (![B_2]: (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_2))) | ~r1_tarski(k2_relat_1('#skF_9'), B_2) | ~r2_hidden('#skF_6'('#skF_7', B_2, '#skF_9'), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_166, c_689])).
% 3.55/1.62  tff(c_704, plain, (![B_157]: (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_157))) | ~r1_tarski(k2_relat_1('#skF_9'), B_157) | ~r2_hidden('#skF_6'('#skF_7', B_157, '#skF_9'), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_117, c_190, c_693])).
% 3.55/1.62  tff(c_707, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_7')), inference(resolution, [status(thm)], [c_704, c_125])).
% 3.55/1.62  tff(c_711, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_580, c_266, c_707])).
% 3.55/1.62  tff(c_712, plain, (~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_116])).
% 3.55/1.62  tff(c_725, plain, (![A_167, B_168, D_169]: ('#skF_5'(A_167, B_168, k1_funct_2(A_167, B_168), D_169)=D_169 | ~r2_hidden(D_169, k1_funct_2(A_167, B_168)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.62  tff(c_736, plain, ('#skF_5'('#skF_7', '#skF_8', k1_funct_2('#skF_7', '#skF_8'), '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_60, c_725])).
% 3.55/1.62  tff(c_834, plain, (![A_188, B_189, D_190]: (r1_tarski(k2_relat_1('#skF_5'(A_188, B_189, k1_funct_2(A_188, B_189), D_190)), B_189) | ~r2_hidden(D_190, k1_funct_2(A_188, B_189)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.62  tff(c_842, plain, (r1_tarski(k2_relat_1('#skF_9'), '#skF_8') | ~r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_736, c_834])).
% 3.55/1.62  tff(c_846, plain, (r1_tarski(k2_relat_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_842])).
% 3.55/1.62  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.62  tff(c_62, plain, (![A_34, B_35]: (~r2_hidden('#skF_1'(A_34, B_35), B_35) | r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.62  tff(c_67, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_62])).
% 3.55/1.62  tff(c_743, plain, (v1_relat_1('#skF_9') | ~r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_736, c_20])).
% 3.55/1.62  tff(c_749, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_743])).
% 3.55/1.62  tff(c_751, plain, (![A_170, B_171, D_172]: (k1_relat_1('#skF_5'(A_170, B_171, k1_funct_2(A_170, B_171), D_172))=A_170 | ~r2_hidden(D_172, k1_funct_2(A_170, B_171)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.62  tff(c_760, plain, (k1_relat_1('#skF_9')='#skF_7' | ~r2_hidden('#skF_9', k1_funct_2('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_736, c_751])).
% 3.55/1.62  tff(c_764, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_760])).
% 3.55/1.62  tff(c_917, plain, (![C_208, B_209]: (r2_hidden('#skF_6'(k1_relat_1(C_208), B_209, C_208), k1_relat_1(C_208)) | v1_funct_2(C_208, k1_relat_1(C_208), B_209) | ~v1_funct_1(C_208) | ~v1_relat_1(C_208))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.55/1.62  tff(c_922, plain, (![B_209]: (r2_hidden('#skF_6'('#skF_7', B_209, '#skF_9'), k1_relat_1('#skF_9')) | v1_funct_2('#skF_9', k1_relat_1('#skF_9'), B_209) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_764, c_917])).
% 3.55/1.62  tff(c_937, plain, (![B_210]: (r2_hidden('#skF_6'('#skF_7', B_210, '#skF_9'), '#skF_7') | v1_funct_2('#skF_9', '#skF_7', B_210))), inference(demodulation, [status(thm), theory('equality')], [c_749, c_117, c_764, c_764, c_922])).
% 3.55/1.62  tff(c_940, plain, (![B_210, B_2]: (r2_hidden('#skF_6'('#skF_7', B_210, '#skF_9'), B_2) | ~r1_tarski('#skF_7', B_2) | v1_funct_2('#skF_9', '#skF_7', B_210))), inference(resolution, [status(thm)], [c_937, c_2])).
% 3.55/1.62  tff(c_769, plain, (![B_173, A_174]: (r2_hidden(k1_funct_1(B_173, A_174), k2_relat_1(B_173)) | ~r2_hidden(A_174, k1_relat_1(B_173)) | ~v1_funct_1(B_173) | ~v1_relat_1(B_173))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.55/1.62  tff(c_772, plain, (![B_173, A_174, B_2]: (r2_hidden(k1_funct_1(B_173, A_174), B_2) | ~r1_tarski(k2_relat_1(B_173), B_2) | ~r2_hidden(A_174, k1_relat_1(B_173)) | ~v1_funct_1(B_173) | ~v1_relat_1(B_173))), inference(resolution, [status(thm)], [c_769, c_2])).
% 3.55/1.62  tff(c_1022, plain, (![C_232, B_233]: (~r2_hidden(k1_funct_1(C_232, '#skF_6'(k1_relat_1(C_232), B_233, C_232)), B_233) | v1_funct_2(C_232, k1_relat_1(C_232), B_233) | ~v1_funct_1(C_232) | ~v1_relat_1(C_232))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.55/1.62  tff(c_1033, plain, (![B_233]: (~r2_hidden(k1_funct_1('#skF_9', '#skF_6'('#skF_7', B_233, '#skF_9')), B_233) | v1_funct_2('#skF_9', k1_relat_1('#skF_9'), B_233) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_764, c_1022])).
% 3.55/1.62  tff(c_1041, plain, (![B_234]: (~r2_hidden(k1_funct_1('#skF_9', '#skF_6'('#skF_7', B_234, '#skF_9')), B_234) | v1_funct_2('#skF_9', '#skF_7', B_234))), inference(demodulation, [status(thm), theory('equality')], [c_749, c_117, c_764, c_1033])).
% 3.55/1.62  tff(c_1045, plain, (![B_2]: (v1_funct_2('#skF_9', '#skF_7', B_2) | ~r1_tarski(k2_relat_1('#skF_9'), B_2) | ~r2_hidden('#skF_6'('#skF_7', B_2, '#skF_9'), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_772, c_1041])).
% 3.55/1.62  tff(c_1082, plain, (![B_237]: (v1_funct_2('#skF_9', '#skF_7', B_237) | ~r1_tarski(k2_relat_1('#skF_9'), B_237) | ~r2_hidden('#skF_6'('#skF_7', B_237, '#skF_9'), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_749, c_117, c_764, c_1045])).
% 3.55/1.62  tff(c_1086, plain, (![B_210]: (~r1_tarski(k2_relat_1('#skF_9'), B_210) | ~r1_tarski('#skF_7', '#skF_7') | v1_funct_2('#skF_9', '#skF_7', B_210))), inference(resolution, [status(thm)], [c_940, c_1082])).
% 3.55/1.62  tff(c_1114, plain, (![B_240]: (~r1_tarski(k2_relat_1('#skF_9'), B_240) | v1_funct_2('#skF_9', '#skF_7', B_240))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_1086])).
% 3.55/1.62  tff(c_1117, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_846, c_1114])).
% 3.55/1.62  tff(c_1125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_712, c_1117])).
% 3.55/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.62  
% 3.55/1.62  Inference rules
% 3.55/1.62  ----------------------
% 3.55/1.62  #Ref     : 0
% 3.55/1.62  #Sup     : 250
% 3.55/1.62  #Fact    : 0
% 3.55/1.62  #Define  : 0
% 3.55/1.62  #Split   : 6
% 3.55/1.62  #Chain   : 0
% 3.55/1.62  #Close   : 0
% 3.55/1.62  
% 3.55/1.62  Ordering : KBO
% 3.55/1.62  
% 3.55/1.62  Simplification rules
% 3.55/1.62  ----------------------
% 3.55/1.62  #Subsume      : 33
% 3.55/1.62  #Demod        : 122
% 3.55/1.62  #Tautology    : 50
% 3.55/1.62  #SimpNegUnit  : 2
% 3.55/1.62  #BackRed      : 0
% 3.55/1.62  
% 3.55/1.62  #Partial instantiations: 0
% 3.55/1.62  #Strategies tried      : 1
% 3.55/1.62  
% 3.55/1.62  Timing (in seconds)
% 3.55/1.62  ----------------------
% 3.55/1.62  Preprocessing        : 0.35
% 3.55/1.62  Parsing              : 0.17
% 3.55/1.62  CNF conversion       : 0.03
% 3.55/1.62  Main loop            : 0.47
% 3.55/1.62  Inferencing          : 0.18
% 3.55/1.62  Reduction            : 0.13
% 3.55/1.62  Demodulation         : 0.09
% 3.55/1.62  BG Simplification    : 0.03
% 3.55/1.62  Subsumption          : 0.09
% 3.55/1.62  Abstraction          : 0.03
% 3.55/1.62  MUC search           : 0.00
% 3.55/1.62  Cooper               : 0.00
% 3.55/1.62  Total                : 0.86
% 3.55/1.62  Index Insertion      : 0.00
% 3.55/1.62  Index Deletion       : 0.00
% 3.55/1.62  Index Matching       : 0.00
% 3.55/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
