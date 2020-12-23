%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:45 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 275 expanded)
%              Number of leaves         :   31 ( 115 expanded)
%              Depth                    :   11
%              Number of atoms          :  162 ( 979 expanded)
%              Number of equality atoms :   53 ( 259 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_30,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_71,plain,(
    ! [C_25,A_26,B_27] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_75,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_71])).

tff(c_91,plain,(
    ! [C_34,A_35,B_36] :
      ( v4_relat_1(C_34,A_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_95,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_91])).

tff(c_26,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_40,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_162,plain,(
    ! [D_48,C_49,B_50,A_51] :
      ( k1_funct_1(k2_funct_1(D_48),k1_funct_1(D_48,C_49)) = C_49
      | k1_xboole_0 = B_50
      | ~ r2_hidden(C_49,A_51)
      | ~ v2_funct_1(D_48)
      | ~ m1_subset_1(D_48,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50)))
      | ~ v1_funct_2(D_48,A_51,B_50)
      | ~ v1_funct_1(D_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_169,plain,(
    ! [D_52,B_53] :
      ( k1_funct_1(k2_funct_1(D_52),k1_funct_1(D_52,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_53
      | ~ v2_funct_1(D_52)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_53)))
      | ~ v1_funct_2(D_52,'#skF_1',B_53)
      | ~ v1_funct_1(D_52) ) ),
    inference(resolution,[status(thm)],[c_30,c_162])).

tff(c_171,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_169])).

tff(c_174,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_171])).

tff(c_175,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_76,plain,(
    ! [B_28,A_29] :
      ( r1_tarski(k1_relat_1(B_28),A_29)
      | ~ v4_relat_1(B_28,A_29)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,(
    ! [B_22,A_23] :
      ( B_22 = A_23
      | ~ r1_tarski(B_22,A_23)
      | ~ r1_tarski(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_83,plain,(
    ! [B_28] :
      ( k1_relat_1(B_28) = k1_xboole_0
      | ~ v4_relat_1(B_28,k1_xboole_0)
      | ~ v1_relat_1(B_28) ) ),
    inference(resolution,[status(thm)],[c_76,c_57])).

tff(c_220,plain,(
    ! [B_58] :
      ( k1_relat_1(B_58) = '#skF_1'
      | ~ v4_relat_1(B_58,'#skF_1')
      | ~ v1_relat_1(B_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_175,c_83])).

tff(c_223,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_95,c_220])).

tff(c_226,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_223])).

tff(c_28,plain,(
    k1_funct_1('#skF_2','#skF_3') = k1_funct_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_138,plain,(
    ! [B_46,A_47] :
      ( k1_funct_1(k2_funct_1(B_46),k1_funct_1(B_46,A_47)) = A_47
      | ~ r2_hidden(A_47,k1_relat_1(B_46))
      | ~ v2_funct_1(B_46)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_156,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_138])).

tff(c_160,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_40,c_34,c_156])).

tff(c_161,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_227,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_161])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_227])).

tff(c_231,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_232,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_233,plain,(
    ! [D_59,B_60] :
      ( k1_funct_1(k2_funct_1(D_59),k1_funct_1(D_59,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = B_60
      | ~ v2_funct_1(D_59)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_60)))
      | ~ v1_funct_2(D_59,'#skF_1',B_60)
      | ~ v1_funct_1(D_59) ) ),
    inference(resolution,[status(thm)],[c_32,c_162])).

tff(c_235,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_233])).

tff(c_238,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_28,c_235])).

tff(c_239,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_238])).

tff(c_259,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_239])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_259])).

tff(c_261,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_282,plain,(
    ! [D_61,C_62,B_63,A_64] :
      ( k1_funct_1(k2_funct_1(D_61),k1_funct_1(D_61,C_62)) = C_62
      | k1_xboole_0 = B_63
      | ~ r2_hidden(C_62,A_64)
      | ~ v2_funct_1(D_61)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63)))
      | ~ v1_funct_2(D_61,A_64,B_63)
      | ~ v1_funct_1(D_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_298,plain,(
    ! [D_67,B_68] :
      ( k1_funct_1(k2_funct_1(D_67),k1_funct_1(D_67,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_68
      | ~ v2_funct_1(D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_68)))
      | ~ v1_funct_2(D_67,'#skF_1',B_68)
      | ~ v1_funct_1(D_67) ) ),
    inference(resolution,[status(thm)],[c_30,c_282])).

tff(c_300,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_298])).

tff(c_303,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_261,c_300])).

tff(c_304,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_303])).

tff(c_342,plain,(
    ! [B_71] :
      ( k1_relat_1(B_71) = '#skF_1'
      | ~ v4_relat_1(B_71,'#skF_1')
      | ~ v1_relat_1(B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_304,c_83])).

tff(c_345,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_95,c_342])).

tff(c_348,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_345])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( k1_funct_1(k2_funct_1(B_7),k1_funct_1(B_7,A_6)) = A_6
      | ~ r2_hidden(A_6,k1_relat_1(B_7))
      | ~ v2_funct_1(B_7)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_269,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_16])).

tff(c_276,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_40,c_34,c_269])).

tff(c_277,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_276])).

tff(c_349,plain,(
    ~ r2_hidden('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_277])).

tff(c_353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:37:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.28  
% 2.30/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.28  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.30/1.28  
% 2.30/1.28  %Foreground sorts:
% 2.30/1.28  
% 2.30/1.28  
% 2.30/1.28  %Background operators:
% 2.30/1.28  
% 2.30/1.28  
% 2.30/1.28  %Foreground operators:
% 2.30/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.30/1.28  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.30/1.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.30/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.30/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.30/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.30/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.30/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.30/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.30/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.30/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.30/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.28  
% 2.30/1.30  tff(f_93, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 2.30/1.30  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.30/1.30  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.30/1.30  tff(f_75, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 2.30/1.30  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.30/1.30  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.30/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.30/1.30  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 2.30/1.30  tff(c_30, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.30/1.30  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.30/1.30  tff(c_71, plain, (![C_25, A_26, B_27]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.30/1.30  tff(c_75, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_71])).
% 2.30/1.30  tff(c_91, plain, (![C_34, A_35, B_36]: (v4_relat_1(C_34, A_35) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.30/1.30  tff(c_95, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_91])).
% 2.30/1.30  tff(c_26, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.30/1.30  tff(c_40, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.30/1.30  tff(c_38, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.30/1.30  tff(c_34, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.30/1.30  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.30/1.30  tff(c_162, plain, (![D_48, C_49, B_50, A_51]: (k1_funct_1(k2_funct_1(D_48), k1_funct_1(D_48, C_49))=C_49 | k1_xboole_0=B_50 | ~r2_hidden(C_49, A_51) | ~v2_funct_1(D_48) | ~m1_subset_1(D_48, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))) | ~v1_funct_2(D_48, A_51, B_50) | ~v1_funct_1(D_48))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.30/1.30  tff(c_169, plain, (![D_52, B_53]: (k1_funct_1(k2_funct_1(D_52), k1_funct_1(D_52, '#skF_4'))='#skF_4' | k1_xboole_0=B_53 | ~v2_funct_1(D_52) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_53))) | ~v1_funct_2(D_52, '#skF_1', B_53) | ~v1_funct_1(D_52))), inference(resolution, [status(thm)], [c_30, c_162])).
% 2.30/1.30  tff(c_171, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_169])).
% 2.30/1.30  tff(c_174, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_171])).
% 2.30/1.30  tff(c_175, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_174])).
% 2.30/1.30  tff(c_76, plain, (![B_28, A_29]: (r1_tarski(k1_relat_1(B_28), A_29) | ~v4_relat_1(B_28, A_29) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.30/1.30  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.30/1.30  tff(c_48, plain, (![B_22, A_23]: (B_22=A_23 | ~r1_tarski(B_22, A_23) | ~r1_tarski(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.30  tff(c_57, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_48])).
% 2.30/1.30  tff(c_83, plain, (![B_28]: (k1_relat_1(B_28)=k1_xboole_0 | ~v4_relat_1(B_28, k1_xboole_0) | ~v1_relat_1(B_28))), inference(resolution, [status(thm)], [c_76, c_57])).
% 2.30/1.30  tff(c_220, plain, (![B_58]: (k1_relat_1(B_58)='#skF_1' | ~v4_relat_1(B_58, '#skF_1') | ~v1_relat_1(B_58))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_175, c_83])).
% 2.30/1.30  tff(c_223, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_95, c_220])).
% 2.30/1.30  tff(c_226, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_223])).
% 2.30/1.30  tff(c_28, plain, (k1_funct_1('#skF_2', '#skF_3')=k1_funct_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.30/1.30  tff(c_138, plain, (![B_46, A_47]: (k1_funct_1(k2_funct_1(B_46), k1_funct_1(B_46, A_47))=A_47 | ~r2_hidden(A_47, k1_relat_1(B_46)) | ~v2_funct_1(B_46) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.30/1.30  tff(c_156, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | ~r2_hidden('#skF_3', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28, c_138])).
% 2.30/1.30  tff(c_160, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | ~r2_hidden('#skF_3', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_40, c_34, c_156])).
% 2.30/1.30  tff(c_161, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_160])).
% 2.30/1.30  tff(c_227, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_161])).
% 2.30/1.30  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_227])).
% 2.30/1.30  tff(c_231, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_174])).
% 2.30/1.30  tff(c_232, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_174])).
% 2.30/1.30  tff(c_233, plain, (![D_59, B_60]: (k1_funct_1(k2_funct_1(D_59), k1_funct_1(D_59, '#skF_3'))='#skF_3' | k1_xboole_0=B_60 | ~v2_funct_1(D_59) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_60))) | ~v1_funct_2(D_59, '#skF_1', B_60) | ~v1_funct_1(D_59))), inference(resolution, [status(thm)], [c_32, c_162])).
% 2.30/1.30  tff(c_235, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_233])).
% 2.30/1.30  tff(c_238, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_28, c_235])).
% 2.30/1.30  tff(c_239, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_232, c_238])).
% 2.30/1.30  tff(c_259, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_231, c_239])).
% 2.30/1.30  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_259])).
% 2.30/1.30  tff(c_261, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_160])).
% 2.30/1.30  tff(c_282, plain, (![D_61, C_62, B_63, A_64]: (k1_funct_1(k2_funct_1(D_61), k1_funct_1(D_61, C_62))=C_62 | k1_xboole_0=B_63 | ~r2_hidden(C_62, A_64) | ~v2_funct_1(D_61) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))) | ~v1_funct_2(D_61, A_64, B_63) | ~v1_funct_1(D_61))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.30/1.30  tff(c_298, plain, (![D_67, B_68]: (k1_funct_1(k2_funct_1(D_67), k1_funct_1(D_67, '#skF_4'))='#skF_4' | k1_xboole_0=B_68 | ~v2_funct_1(D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_68))) | ~v1_funct_2(D_67, '#skF_1', B_68) | ~v1_funct_1(D_67))), inference(resolution, [status(thm)], [c_30, c_282])).
% 2.30/1.30  tff(c_300, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_298])).
% 2.30/1.30  tff(c_303, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_261, c_300])).
% 2.30/1.30  tff(c_304, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_26, c_303])).
% 2.30/1.30  tff(c_342, plain, (![B_71]: (k1_relat_1(B_71)='#skF_1' | ~v4_relat_1(B_71, '#skF_1') | ~v1_relat_1(B_71))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_304, c_83])).
% 2.30/1.30  tff(c_345, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_95, c_342])).
% 2.30/1.30  tff(c_348, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_345])).
% 2.30/1.30  tff(c_16, plain, (![B_7, A_6]: (k1_funct_1(k2_funct_1(B_7), k1_funct_1(B_7, A_6))=A_6 | ~r2_hidden(A_6, k1_relat_1(B_7)) | ~v2_funct_1(B_7) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.30/1.30  tff(c_269, plain, ('#skF_3'='#skF_4' | ~r2_hidden('#skF_4', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_261, c_16])).
% 2.30/1.30  tff(c_276, plain, ('#skF_3'='#skF_4' | ~r2_hidden('#skF_4', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_40, c_34, c_269])).
% 2.30/1.30  tff(c_277, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_276])).
% 2.30/1.30  tff(c_349, plain, (~r2_hidden('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_348, c_277])).
% 2.30/1.30  tff(c_353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_349])).
% 2.30/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.30  
% 2.30/1.30  Inference rules
% 2.30/1.30  ----------------------
% 2.30/1.30  #Ref     : 0
% 2.30/1.30  #Sup     : 61
% 2.30/1.30  #Fact    : 0
% 2.30/1.30  #Define  : 0
% 2.30/1.30  #Split   : 2
% 2.30/1.30  #Chain   : 0
% 2.30/1.30  #Close   : 0
% 2.30/1.30  
% 2.30/1.30  Ordering : KBO
% 2.30/1.30  
% 2.30/1.30  Simplification rules
% 2.30/1.30  ----------------------
% 2.30/1.30  #Subsume      : 4
% 2.30/1.30  #Demod        : 61
% 2.30/1.30  #Tautology    : 29
% 2.30/1.30  #SimpNegUnit  : 5
% 2.30/1.30  #BackRed      : 14
% 2.30/1.30  
% 2.30/1.30  #Partial instantiations: 0
% 2.30/1.30  #Strategies tried      : 1
% 2.30/1.30  
% 2.30/1.30  Timing (in seconds)
% 2.30/1.30  ----------------------
% 2.60/1.30  Preprocessing        : 0.30
% 2.60/1.30  Parsing              : 0.16
% 2.60/1.30  CNF conversion       : 0.02
% 2.60/1.30  Main loop            : 0.23
% 2.60/1.30  Inferencing          : 0.08
% 2.60/1.30  Reduction            : 0.07
% 2.60/1.30  Demodulation         : 0.05
% 2.60/1.30  BG Simplification    : 0.01
% 2.60/1.30  Subsumption          : 0.04
% 2.60/1.30  Abstraction          : 0.01
% 2.60/1.30  MUC search           : 0.00
% 2.60/1.30  Cooper               : 0.00
% 2.60/1.30  Total                : 0.57
% 2.60/1.30  Index Insertion      : 0.00
% 2.60/1.30  Index Deletion       : 0.00
% 2.60/1.30  Index Matching       : 0.00
% 2.60/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
