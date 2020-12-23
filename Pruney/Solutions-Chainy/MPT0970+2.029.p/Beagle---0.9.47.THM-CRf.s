%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:23 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 555 expanded)
%              Number of leaves         :   31 ( 207 expanded)
%              Depth                    :   12
%              Number of atoms          :  136 (1797 expanded)
%              Number of equality atoms :   59 ( 800 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
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

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_28,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_83,plain,(
    ! [A_47,B_48,C_49] :
      ( k2_relset_1(A_47,B_48,C_49) = k2_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_87,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_83])).

tff(c_38,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_92,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_38])).

tff(c_113,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden('#skF_1'(A_62,B_63,C_64),B_63)
      | k2_relset_1(A_62,B_63,C_64) = B_63
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_115,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_113])).

tff(c_117,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_115])).

tff(c_118,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_117])).

tff(c_48,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_6'(D_34),'#skF_3')
      | ~ r2_hidden(D_34,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_78,plain,(
    ! [A_44,B_45,C_46] :
      ( k1_relset_1(A_44,B_45,C_46) = k1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_82,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_78])).

tff(c_136,plain,(
    ! [B_68,A_69,C_70] :
      ( k1_xboole_0 = B_68
      | k1_relset_1(A_69,B_68,C_70) = A_69
      | ~ v1_funct_2(C_70,A_69,B_68)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_139,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_136])).

tff(c_142,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_82,c_139])).

tff(c_143,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_58,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_58])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    ! [D_34] :
      ( k1_funct_1('#skF_5','#skF_6'(D_34)) = D_34
      | ~ r2_hidden(D_34,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_100,plain,(
    ! [B_56,A_57] :
      ( r2_hidden(k4_tarski(B_56,k1_funct_1(A_57,B_56)),A_57)
      | ~ r2_hidden(B_56,k1_relat_1(A_57))
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_103,plain,(
    ! [D_34] :
      ( r2_hidden(k4_tarski('#skF_6'(D_34),D_34),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_34),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(D_34,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_100])).

tff(c_105,plain,(
    ! [D_34] :
      ( r2_hidden(k4_tarski('#skF_6'(D_34),D_34),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_34),k1_relat_1('#skF_5'))
      | ~ r2_hidden(D_34,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_44,c_103])).

tff(c_144,plain,(
    ! [D_34] :
      ( r2_hidden(k4_tarski('#skF_6'(D_34),D_34),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_34),'#skF_3')
      | ~ r2_hidden(D_34,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_105])).

tff(c_173,plain,(
    ! [E_73,A_74,B_75,C_76] :
      ( ~ r2_hidden(k4_tarski(E_73,'#skF_1'(A_74,B_75,C_76)),C_76)
      | k2_relset_1(A_74,B_75,C_76) = B_75
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_200,plain,(
    ! [A_84,B_85] :
      ( k2_relset_1(A_84,B_85,'#skF_5') = B_85
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ r2_hidden('#skF_6'('#skF_1'(A_84,B_85,'#skF_5')),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_84,B_85,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_144,c_173])).

tff(c_209,plain,(
    ! [A_86,B_87] :
      ( k2_relset_1(A_86,B_87,'#skF_5') = B_87
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ r2_hidden('#skF_1'(A_86,B_87,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_200])).

tff(c_212,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_209])).

tff(c_215,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_87,c_212])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_215])).

tff(c_218,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_2,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_228,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_218,c_2])).

tff(c_28,plain,(
    ! [C_30,A_28] :
      ( k1_xboole_0 = C_30
      | ~ v1_funct_2(C_30,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_270,plain,(
    ! [C_97,A_98] :
      ( C_97 = '#skF_4'
      | ~ v1_funct_2(C_97,A_98,'#skF_4')
      | A_98 = '#skF_4'
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_218,c_218,c_218,c_28])).

tff(c_273,plain,
    ( '#skF_5' = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_270])).

tff(c_276,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_273])).

tff(c_277,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_219,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_278,plain,(
    k1_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_219])).

tff(c_284,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_42])).

tff(c_281,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_82])).

tff(c_283,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_40])).

tff(c_34,plain,(
    ! [B_29,C_30] :
      ( k1_relset_1(k1_xboole_0,B_29,C_30) = k1_xboole_0
      | ~ v1_funct_2(C_30,k1_xboole_0,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_334,plain,(
    ! [B_104,C_105] :
      ( k1_relset_1('#skF_4',B_104,C_105) = '#skF_4'
      | ~ v1_funct_2(C_105,'#skF_4',B_104)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_104))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_218,c_218,c_218,c_34])).

tff(c_337,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_283,c_334])).

tff(c_340,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_281,c_337])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_340])).

tff(c_343,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_349,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_92])).

tff(c_362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:48:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.32  
% 2.17/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.33  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6
% 2.17/1.33  
% 2.17/1.33  %Foreground sorts:
% 2.17/1.33  
% 2.17/1.33  
% 2.17/1.33  %Background operators:
% 2.17/1.33  
% 2.17/1.33  
% 2.17/1.33  %Foreground operators:
% 2.17/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.17/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.17/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.17/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.17/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.17/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.17/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.33  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.17/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.33  
% 2.55/1.34  tff(f_107, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 2.55/1.34  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.55/1.34  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 2.55/1.34  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.55/1.34  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.55/1.34  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.55/1.34  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 2.55/1.34  tff(f_28, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.55/1.34  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.55/1.34  tff(c_83, plain, (![A_47, B_48, C_49]: (k2_relset_1(A_47, B_48, C_49)=k2_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.55/1.34  tff(c_87, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_83])).
% 2.55/1.34  tff(c_38, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.55/1.34  tff(c_92, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_38])).
% 2.55/1.34  tff(c_113, plain, (![A_62, B_63, C_64]: (r2_hidden('#skF_1'(A_62, B_63, C_64), B_63) | k2_relset_1(A_62, B_63, C_64)=B_63 | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.55/1.34  tff(c_115, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_40, c_113])).
% 2.55/1.34  tff(c_117, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_115])).
% 2.55/1.34  tff(c_118, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_92, c_117])).
% 2.55/1.34  tff(c_48, plain, (![D_34]: (r2_hidden('#skF_6'(D_34), '#skF_3') | ~r2_hidden(D_34, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.55/1.34  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.55/1.34  tff(c_78, plain, (![A_44, B_45, C_46]: (k1_relset_1(A_44, B_45, C_46)=k1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.55/1.34  tff(c_82, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_78])).
% 2.55/1.34  tff(c_136, plain, (![B_68, A_69, C_70]: (k1_xboole_0=B_68 | k1_relset_1(A_69, B_68, C_70)=A_69 | ~v1_funct_2(C_70, A_69, B_68) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.55/1.34  tff(c_139, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_136])).
% 2.55/1.34  tff(c_142, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_82, c_139])).
% 2.55/1.34  tff(c_143, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_142])).
% 2.55/1.34  tff(c_58, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.55/1.34  tff(c_62, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_58])).
% 2.55/1.34  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.55/1.34  tff(c_46, plain, (![D_34]: (k1_funct_1('#skF_5', '#skF_6'(D_34))=D_34 | ~r2_hidden(D_34, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.55/1.34  tff(c_100, plain, (![B_56, A_57]: (r2_hidden(k4_tarski(B_56, k1_funct_1(A_57, B_56)), A_57) | ~r2_hidden(B_56, k1_relat_1(A_57)) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.55/1.34  tff(c_103, plain, (![D_34]: (r2_hidden(k4_tarski('#skF_6'(D_34), D_34), '#skF_5') | ~r2_hidden('#skF_6'(D_34), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(D_34, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_100])).
% 2.55/1.34  tff(c_105, plain, (![D_34]: (r2_hidden(k4_tarski('#skF_6'(D_34), D_34), '#skF_5') | ~r2_hidden('#skF_6'(D_34), k1_relat_1('#skF_5')) | ~r2_hidden(D_34, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_44, c_103])).
% 2.55/1.34  tff(c_144, plain, (![D_34]: (r2_hidden(k4_tarski('#skF_6'(D_34), D_34), '#skF_5') | ~r2_hidden('#skF_6'(D_34), '#skF_3') | ~r2_hidden(D_34, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_105])).
% 2.55/1.34  tff(c_173, plain, (![E_73, A_74, B_75, C_76]: (~r2_hidden(k4_tarski(E_73, '#skF_1'(A_74, B_75, C_76)), C_76) | k2_relset_1(A_74, B_75, C_76)=B_75 | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.55/1.34  tff(c_200, plain, (![A_84, B_85]: (k2_relset_1(A_84, B_85, '#skF_5')=B_85 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~r2_hidden('#skF_6'('#skF_1'(A_84, B_85, '#skF_5')), '#skF_3') | ~r2_hidden('#skF_1'(A_84, B_85, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_144, c_173])).
% 2.55/1.34  tff(c_209, plain, (![A_86, B_87]: (k2_relset_1(A_86, B_87, '#skF_5')=B_87 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~r2_hidden('#skF_1'(A_86, B_87, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_200])).
% 2.55/1.34  tff(c_212, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4' | ~r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_40, c_209])).
% 2.55/1.34  tff(c_215, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_87, c_212])).
% 2.55/1.34  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_215])).
% 2.55/1.34  tff(c_218, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_142])).
% 2.55/1.34  tff(c_2, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.55/1.34  tff(c_228, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_218, c_218, c_2])).
% 2.55/1.34  tff(c_28, plain, (![C_30, A_28]: (k1_xboole_0=C_30 | ~v1_funct_2(C_30, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.55/1.34  tff(c_270, plain, (![C_97, A_98]: (C_97='#skF_4' | ~v1_funct_2(C_97, A_98, '#skF_4') | A_98='#skF_4' | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_218, c_218, c_218, c_28])).
% 2.55/1.34  tff(c_273, plain, ('#skF_5'='#skF_4' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_270])).
% 2.55/1.34  tff(c_276, plain, ('#skF_5'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_273])).
% 2.55/1.34  tff(c_277, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_276])).
% 2.55/1.34  tff(c_219, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitRight, [status(thm)], [c_142])).
% 2.55/1.34  tff(c_278, plain, (k1_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_277, c_219])).
% 2.55/1.34  tff(c_284, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_42])).
% 2.55/1.34  tff(c_281, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_82])).
% 2.55/1.34  tff(c_283, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_277, c_40])).
% 2.55/1.34  tff(c_34, plain, (![B_29, C_30]: (k1_relset_1(k1_xboole_0, B_29, C_30)=k1_xboole_0 | ~v1_funct_2(C_30, k1_xboole_0, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.55/1.34  tff(c_334, plain, (![B_104, C_105]: (k1_relset_1('#skF_4', B_104, C_105)='#skF_4' | ~v1_funct_2(C_105, '#skF_4', B_104) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_104))))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_218, c_218, c_218, c_34])).
% 2.55/1.34  tff(c_337, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_283, c_334])).
% 2.55/1.34  tff(c_340, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_284, c_281, c_337])).
% 2.55/1.34  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_278, c_340])).
% 2.55/1.34  tff(c_343, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_276])).
% 2.55/1.34  tff(c_349, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_343, c_92])).
% 2.55/1.34  tff(c_362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_228, c_349])).
% 2.55/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.34  
% 2.55/1.34  Inference rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Ref     : 0
% 2.55/1.34  #Sup     : 62
% 2.55/1.34  #Fact    : 0
% 2.55/1.34  #Define  : 0
% 2.55/1.34  #Split   : 4
% 2.55/1.34  #Chain   : 0
% 2.55/1.34  #Close   : 0
% 2.55/1.34  
% 2.55/1.34  Ordering : KBO
% 2.55/1.34  
% 2.55/1.34  Simplification rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Subsume      : 5
% 2.55/1.34  #Demod        : 84
% 2.55/1.34  #Tautology    : 33
% 2.55/1.34  #SimpNegUnit  : 3
% 2.55/1.34  #BackRed      : 32
% 2.55/1.34  
% 2.55/1.34  #Partial instantiations: 0
% 2.55/1.35  #Strategies tried      : 1
% 2.55/1.35  
% 2.55/1.35  Timing (in seconds)
% 2.55/1.35  ----------------------
% 2.55/1.35  Preprocessing        : 0.33
% 2.55/1.35  Parsing              : 0.17
% 2.55/1.35  CNF conversion       : 0.02
% 2.55/1.35  Main loop            : 0.26
% 2.55/1.35  Inferencing          : 0.09
% 2.55/1.35  Reduction            : 0.08
% 2.55/1.35  Demodulation         : 0.05
% 2.55/1.35  BG Simplification    : 0.02
% 2.55/1.35  Subsumption          : 0.04
% 2.55/1.35  Abstraction          : 0.02
% 2.55/1.35  MUC search           : 0.00
% 2.55/1.35  Cooper               : 0.00
% 2.55/1.35  Total                : 0.62
% 2.55/1.35  Index Insertion      : 0.00
% 2.55/1.35  Index Deletion       : 0.00
% 2.55/1.35  Index Matching       : 0.00
% 2.55/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
