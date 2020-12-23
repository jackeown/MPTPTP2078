%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0979+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:11 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 571 expanded)
%              Number of leaves         :   27 ( 192 expanded)
%              Depth                    :   13
%              Number of atoms          :  281 (2169 expanded)
%              Number of equality atoms :  106 ( 957 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v2_funct_1(C)
          <=> ! [D,E] :
                ( ( r2_hidden(D,A)
                  & r2_hidden(E,A)
                  & k1_funct_1(C,D) = k1_funct_1(C,E) )
               => D = E ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_57,plain,(
    ! [C_23,A_24,B_25] :
      ( v1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_61,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_57])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_62,plain,(
    ! [A_26] :
      ( '#skF_2'(A_26) != '#skF_1'(A_26)
      | v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,
    ( '#skF_7' != '#skF_6'
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_55,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_65,plain,
    ( '#skF_2'('#skF_5') != '#skF_1'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_55])).

tff(c_68,plain,(
    '#skF_2'('#skF_5') != '#skF_1'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_34,c_65])).

tff(c_28,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_32,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_71,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_relset_1(A_29,B_30,C_31) = k1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_75,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_71])).

tff(c_112,plain,(
    ! [B_42,A_43,C_44] :
      ( k1_xboole_0 = B_42
      | k1_relset_1(A_43,B_42,C_44) = A_43
      | ~ v1_funct_2(C_44,A_43,B_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_43,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_115,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_112])).

tff(c_118,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_75,c_115])).

tff(c_119,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_118])).

tff(c_24,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(A_7),k1_relat_1(A_7))
      | v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_127,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_3')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_24])).

tff(c_134,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_3')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_34,c_127])).

tff(c_135,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_134])).

tff(c_22,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_2'(A_7),k1_relat_1(A_7))
      | v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_124,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_3')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_22])).

tff(c_131,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_3')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_34,c_124])).

tff(c_132,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_131])).

tff(c_20,plain,(
    ! [A_7] :
      ( k1_funct_1(A_7,'#skF_2'(A_7)) = k1_funct_1(A_7,'#skF_1'(A_7))
      | v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_54,plain,(
    ! [E_22,D_21] :
      ( v2_funct_1('#skF_5')
      | E_22 = D_21
      | k1_funct_1('#skF_5',E_22) != k1_funct_1('#skF_5',D_21)
      | ~ r2_hidden(E_22,'#skF_3')
      | ~ r2_hidden(D_21,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_99,plain,(
    ! [E_40,D_41] :
      ( E_40 = D_41
      | k1_funct_1('#skF_5',E_40) != k1_funct_1('#skF_5',D_41)
      | ~ r2_hidden(E_40,'#skF_3')
      | ~ r2_hidden(D_41,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_54])).

tff(c_102,plain,(
    ! [D_41] :
      ( D_41 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_41) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_3')
      | ~ r2_hidden(D_41,'#skF_3')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_99])).

tff(c_107,plain,(
    ! [D_41] :
      ( D_41 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_41) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_3')
      | ~ r2_hidden(D_41,'#skF_3')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_34,c_102])).

tff(c_108,plain,(
    ! [D_41] :
      ( D_41 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_41) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_3')
      | ~ r2_hidden(D_41,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_107])).

tff(c_159,plain,(
    ! [D_41] :
      ( D_41 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_41) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden(D_41,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_108])).

tff(c_162,plain,
    ( '#skF_2'('#skF_5') = '#skF_1'('#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_5'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_159])).

tff(c_164,plain,(
    '#skF_2'('#skF_5') = '#skF_1'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_162])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_164])).

tff(c_168,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_167,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_173,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_167])).

tff(c_184,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_30])).

tff(c_185,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_189,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_184,c_185])).

tff(c_190,plain,(
    ! [A_54] :
      ( '#skF_2'(A_54) != '#skF_1'(A_54)
      | v2_funct_1(A_54)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_193,plain,
    ( '#skF_2'('#skF_5') != '#skF_1'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_190,c_55])).

tff(c_196,plain,(
    '#skF_2'('#skF_5') != '#skF_1'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_34,c_193])).

tff(c_178,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_32])).

tff(c_203,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_207,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_184,c_203])).

tff(c_12,plain,(
    ! [B_5,C_6] :
      ( k1_relset_1(k1_xboole_0,B_5,C_6) = k1_xboole_0
      | ~ v1_funct_2(C_6,k1_xboole_0,B_5)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_231,plain,(
    ! [B_64,C_65] :
      ( k1_relset_1('#skF_4',B_64,C_65) = '#skF_4'
      | ~ v1_funct_2(C_65,'#skF_4',B_64)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_64))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_168,c_168,c_168,c_12])).

tff(c_234,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_184,c_231])).

tff(c_237,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_207,c_234])).

tff(c_261,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_24])).

tff(c_268,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_34,c_261])).

tff(c_269,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_268])).

tff(c_264,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_22])).

tff(c_271,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_34,c_264])).

tff(c_272,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_271])).

tff(c_238,plain,(
    ! [E_22,D_21] :
      ( v2_funct_1('#skF_5')
      | E_22 = D_21
      | k1_funct_1('#skF_5',E_22) != k1_funct_1('#skF_5',D_21)
      | ~ r2_hidden(E_22,'#skF_4')
      | ~ r2_hidden(D_21,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_173,c_54])).

tff(c_244,plain,(
    ! [E_66,D_67] :
      ( E_66 = D_67
      | k1_funct_1('#skF_5',E_66) != k1_funct_1('#skF_5',D_67)
      | ~ r2_hidden(E_66,'#skF_4')
      | ~ r2_hidden(D_67,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_238])).

tff(c_247,plain,(
    ! [D_67] :
      ( D_67 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_67) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(D_67,'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_244])).

tff(c_252,plain,(
    ! [D_67] :
      ( D_67 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_67) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(D_67,'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_34,c_247])).

tff(c_253,plain,(
    ! [D_67] :
      ( D_67 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_67) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(D_67,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_252])).

tff(c_308,plain,(
    ! [D_67] :
      ( D_67 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_67) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden(D_67,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_253])).

tff(c_311,plain,
    ( '#skF_2'('#skF_5') = '#skF_1'('#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_5'),'#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_308])).

tff(c_313,plain,(
    '#skF_2'('#skF_5') = '#skF_1'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_311])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_313])).

tff(c_316,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_317,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_42,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_322,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_42])).

tff(c_329,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_333,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_329])).

tff(c_318,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_338,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_342,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_338])).

tff(c_361,plain,(
    ! [B_93,A_94,C_95] :
      ( k1_xboole_0 = B_93
      | k1_relset_1(A_94,B_93,C_95) = A_94
      | ~ v1_funct_2(C_95,A_94,B_93)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_364,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_361])).

tff(c_367,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_342,c_364])).

tff(c_368,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_318,c_367])).

tff(c_40,plain,
    ( r2_hidden('#skF_7','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_320,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_40])).

tff(c_38,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_324,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_38])).

tff(c_402,plain,(
    ! [C_99,B_100,A_101] :
      ( C_99 = B_100
      | k1_funct_1(A_101,C_99) != k1_funct_1(A_101,B_100)
      | ~ r2_hidden(C_99,k1_relat_1(A_101))
      | ~ r2_hidden(B_100,k1_relat_1(A_101))
      | ~ v2_funct_1(A_101)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_408,plain,(
    ! [B_100] :
      ( B_100 = '#skF_7'
      | k1_funct_1('#skF_5',B_100) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
      | ~ r2_hidden(B_100,k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_402])).

tff(c_415,plain,(
    ! [B_102] :
      ( B_102 = '#skF_7'
      | k1_funct_1('#skF_5',B_102) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden(B_102,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_34,c_317,c_368,c_320,c_368,c_408])).

tff(c_418,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_322,c_415])).

tff(c_425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_418])).

tff(c_427,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_426,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_432,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_426])).

tff(c_445,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_432,c_42])).

tff(c_446,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_30])).

tff(c_447,plain,(
    ! [C_103,A_104,B_105] :
      ( v1_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_451,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_446,c_447])).

tff(c_437,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_32])).

tff(c_461,plain,(
    ! [A_109,B_110,C_111] :
      ( k1_relset_1(A_109,B_110,C_111) = k1_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_465,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_446,c_461])).

tff(c_492,plain,(
    ! [B_116,C_117] :
      ( k1_relset_1('#skF_4',B_116,C_117) = '#skF_4'
      | ~ v1_funct_2(C_117,'#skF_4',B_116)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_116))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_427,c_427,c_427,c_12])).

tff(c_495,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_446,c_492])).

tff(c_498,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_465,c_495])).

tff(c_443,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_432,c_40])).

tff(c_453,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_38])).

tff(c_552,plain,(
    ! [C_126,B_127,A_128] :
      ( C_126 = B_127
      | k1_funct_1(A_128,C_126) != k1_funct_1(A_128,B_127)
      | ~ r2_hidden(C_126,k1_relat_1(A_128))
      | ~ r2_hidden(B_127,k1_relat_1(A_128))
      | ~ v2_funct_1(A_128)
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_558,plain,(
    ! [B_127] :
      ( B_127 = '#skF_7'
      | k1_funct_1('#skF_5',B_127) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
      | ~ r2_hidden(B_127,k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_552])).

tff(c_565,plain,(
    ! [B_129] :
      ( B_129 = '#skF_7'
      | k1_funct_1('#skF_5',B_129) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden(B_129,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_34,c_317,c_498,c_443,c_498,c_558])).

tff(c_568,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_445,c_565])).

tff(c_575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_568])).

%------------------------------------------------------------------------------
