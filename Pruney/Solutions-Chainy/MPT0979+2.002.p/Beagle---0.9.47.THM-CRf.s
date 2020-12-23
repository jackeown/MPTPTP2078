%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:54 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 602 expanded)
%              Number of leaves         :   28 ( 202 expanded)
%              Depth                    :   13
%              Number of atoms          :  302 (2231 expanded)
%              Number of equality atoms :  108 ( 958 expanded)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_93,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_49,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
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

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_60,plain,(
    ! [B_27,A_28] :
      ( v1_relat_1(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28))
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_60])).

tff(c_66,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_63])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_67,plain,(
    ! [A_29] :
      ( '#skF_2'(A_29) != '#skF_1'(A_29)
      | v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,
    ( '#skF_7' != '#skF_6'
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_57,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_70,plain,
    ( '#skF_2'('#skF_5') != '#skF_1'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_67,c_57])).

tff(c_73,plain,(
    '#skF_2'('#skF_5') != '#skF_1'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_36,c_70])).

tff(c_30,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_34,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_77,plain,(
    ! [A_33,B_34,C_35] :
      ( k1_relset_1(A_33,B_34,C_35) = k1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_81,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_77])).

tff(c_116,plain,(
    ! [B_45,A_46,C_47] :
      ( k1_xboole_0 = B_45
      | k1_relset_1(A_46,B_45,C_47) = A_46
      | ~ v1_funct_2(C_47,A_46,B_45)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_46,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_119,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_116])).

tff(c_122,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_81,c_119])).

tff(c_123,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_122])).

tff(c_14,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_1'(A_6),k1_relat_1(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_128,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_3')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_14])).

tff(c_135,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_3')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_36,c_128])).

tff(c_136,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_135])).

tff(c_12,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),k1_relat_1(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_131,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_3')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_12])).

tff(c_138,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_3')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_36,c_131])).

tff(c_139,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_138])).

tff(c_92,plain,(
    ! [A_38] :
      ( k1_funct_1(A_38,'#skF_2'(A_38)) = k1_funct_1(A_38,'#skF_1'(A_38))
      | v2_funct_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_56,plain,(
    ! [E_24,D_23] :
      ( v2_funct_1('#skF_5')
      | E_24 = D_23
      | k1_funct_1('#skF_5',E_24) != k1_funct_1('#skF_5',D_23)
      | ~ r2_hidden(E_24,'#skF_3')
      | ~ r2_hidden(D_23,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_82,plain,(
    ! [E_24,D_23] :
      ( E_24 = D_23
      | k1_funct_1('#skF_5',E_24) != k1_funct_1('#skF_5',D_23)
      | ~ r2_hidden(E_24,'#skF_3')
      | ~ r2_hidden(D_23,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_56])).

tff(c_98,plain,(
    ! [D_23] :
      ( D_23 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_23) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_3')
      | ~ r2_hidden(D_23,'#skF_3')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_82])).

tff(c_107,plain,(
    ! [D_23] :
      ( D_23 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_23) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_3')
      | ~ r2_hidden(D_23,'#skF_3')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_36,c_98])).

tff(c_108,plain,(
    ! [D_23] :
      ( D_23 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_23) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_3')
      | ~ r2_hidden(D_23,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_107])).

tff(c_154,plain,(
    ! [D_23] :
      ( D_23 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_23) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden(D_23,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_108])).

tff(c_157,plain,
    ( '#skF_2'('#skF_5') = '#skF_1'('#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_5'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_154])).

tff(c_159,plain,(
    '#skF_2'('#skF_5') = '#skF_1'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_157])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_159])).

tff(c_163,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_162,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_168,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_162])).

tff(c_181,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_32])).

tff(c_182,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_185,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_181,c_182])).

tff(c_188,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_185])).

tff(c_189,plain,(
    ! [A_55] :
      ( '#skF_2'(A_55) != '#skF_1'(A_55)
      | v2_funct_1(A_55)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_192,plain,
    ( '#skF_2'('#skF_5') != '#skF_1'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_189,c_57])).

tff(c_195,plain,
    ( '#skF_2'('#skF_5') != '#skF_1'('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_192])).

tff(c_197,plain,(
    '#skF_2'('#skF_5') != '#skF_1'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_195])).

tff(c_173,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_34])).

tff(c_207,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_211,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_181,c_207])).

tff(c_26,plain,(
    ! [B_17,C_18] :
      ( k1_relset_1(k1_xboole_0,B_17,C_18) = k1_xboole_0
      | ~ v1_funct_2(C_18,k1_xboole_0,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_249,plain,(
    ! [B_67,C_68] :
      ( k1_relset_1('#skF_4',B_67,C_68) = '#skF_4'
      | ~ v1_funct_2(C_68,'#skF_4',B_67)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_67))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_163,c_163,c_163,c_26])).

tff(c_252,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_181,c_249])).

tff(c_255,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_211,c_252])).

tff(c_260,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_14])).

tff(c_267,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_36,c_260])).

tff(c_268,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_267])).

tff(c_263,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_12])).

tff(c_270,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_36,c_263])).

tff(c_271,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_270])).

tff(c_218,plain,(
    ! [A_64] :
      ( k1_funct_1(A_64,'#skF_2'(A_64)) = k1_funct_1(A_64,'#skF_1'(A_64))
      | v2_funct_1(A_64)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_199,plain,(
    ! [E_24,D_23] :
      ( v2_funct_1('#skF_5')
      | E_24 = D_23
      | k1_funct_1('#skF_5',E_24) != k1_funct_1('#skF_5',D_23)
      | ~ r2_hidden(E_24,'#skF_4')
      | ~ r2_hidden(D_23,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_168,c_56])).

tff(c_200,plain,(
    ! [E_24,D_23] :
      ( E_24 = D_23
      | k1_funct_1('#skF_5',E_24) != k1_funct_1('#skF_5',D_23)
      | ~ r2_hidden(E_24,'#skF_4')
      | ~ r2_hidden(D_23,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_199])).

tff(c_224,plain,(
    ! [D_23] :
      ( D_23 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_23) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(D_23,'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_200])).

tff(c_233,plain,(
    ! [D_23] :
      ( D_23 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_23) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(D_23,'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_36,c_224])).

tff(c_234,plain,(
    ! [D_23] :
      ( D_23 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_23) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(D_23,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_233])).

tff(c_307,plain,(
    ! [D_23] :
      ( D_23 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_23) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden(D_23,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_234])).

tff(c_310,plain,
    ( '#skF_2'('#skF_5') = '#skF_1'('#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_5'),'#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_307])).

tff(c_312,plain,(
    '#skF_2'('#skF_5') = '#skF_1'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_310])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_312])).

tff(c_315,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_316,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_44,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_322,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_44])).

tff(c_323,plain,(
    ! [B_79,A_80] :
      ( v1_relat_1(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_326,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_323])).

tff(c_329,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_326])).

tff(c_317,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_340,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_344,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_340])).

tff(c_363,plain,(
    ! [B_95,A_96,C_97] :
      ( k1_xboole_0 = B_95
      | k1_relset_1(A_96,B_95,C_97) = A_96
      | ~ v1_funct_2(C_97,A_96,B_95)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_366,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_363])).

tff(c_369,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_344,c_366])).

tff(c_370,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_317,c_369])).

tff(c_42,plain,
    ( r2_hidden('#skF_7','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_320,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_42])).

tff(c_40,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_331,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_40])).

tff(c_403,plain,(
    ! [C_101,B_102,A_103] :
      ( C_101 = B_102
      | k1_funct_1(A_103,C_101) != k1_funct_1(A_103,B_102)
      | ~ r2_hidden(C_101,k1_relat_1(A_103))
      | ~ r2_hidden(B_102,k1_relat_1(A_103))
      | ~ v2_funct_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_409,plain,(
    ! [B_102] :
      ( B_102 = '#skF_7'
      | k1_funct_1('#skF_5',B_102) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
      | ~ r2_hidden(B_102,k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_403])).

tff(c_416,plain,(
    ! [B_104] :
      ( B_104 = '#skF_7'
      | k1_funct_1('#skF_5',B_104) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden(B_104,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_36,c_316,c_370,c_320,c_370,c_409])).

tff(c_419,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_322,c_416])).

tff(c_426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_419])).

tff(c_428,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_427,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_433,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_427])).

tff(c_445,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_433,c_44])).

tff(c_448,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_32])).

tff(c_455,plain,(
    ! [B_107,A_108] :
      ( v1_relat_1(B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_108))
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_458,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_448,c_455])).

tff(c_461,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_458])).

tff(c_438,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_34])).

tff(c_467,plain,(
    ! [A_113,B_114,C_115] :
      ( k1_relset_1(A_113,B_114,C_115) = k1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_471,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_448,c_467])).

tff(c_496,plain,(
    ! [B_119,C_120] :
      ( k1_relset_1('#skF_4',B_119,C_120) = '#skF_4'
      | ~ v1_funct_2(C_120,'#skF_4',B_119)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_119))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_428,c_428,c_428,c_26])).

tff(c_499,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_448,c_496])).

tff(c_502,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_471,c_499])).

tff(c_447,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_433,c_42])).

tff(c_450,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_40])).

tff(c_556,plain,(
    ! [C_129,B_130,A_131] :
      ( C_129 = B_130
      | k1_funct_1(A_131,C_129) != k1_funct_1(A_131,B_130)
      | ~ r2_hidden(C_129,k1_relat_1(A_131))
      | ~ r2_hidden(B_130,k1_relat_1(A_131))
      | ~ v2_funct_1(A_131)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_562,plain,(
    ! [B_130] :
      ( B_130 = '#skF_7'
      | k1_funct_1('#skF_5',B_130) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
      | ~ r2_hidden(B_130,k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_556])).

tff(c_569,plain,(
    ! [B_132] :
      ( B_132 = '#skF_7'
      | k1_funct_1('#skF_5',B_132) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden(B_132,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_36,c_316,c_502,c_447,c_502,c_562])).

tff(c_575,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_445,c_569])).

tff(c_583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_575])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:03:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.45  
% 2.85/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.45  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.85/1.45  
% 2.85/1.45  %Foreground sorts:
% 2.85/1.45  
% 2.85/1.45  
% 2.85/1.45  %Background operators:
% 2.85/1.45  
% 2.85/1.45  
% 2.85/1.45  %Foreground operators:
% 2.85/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.85/1.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.85/1.45  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.85/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.85/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.85/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.85/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.85/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.85/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.85/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.85/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.85/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.85/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.85/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.45  
% 2.97/1.47  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.97/1.47  tff(f_93, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (v2_funct_1(C) <=> (![D, E]: (((r2_hidden(D, A) & r2_hidden(E, A)) & (k1_funct_1(C, D) = k1_funct_1(C, E))) => (D = E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_funct_2)).
% 2.97/1.47  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.97/1.47  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 2.97/1.47  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.97/1.47  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.97/1.47  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.97/1.47  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.97/1.47  tff(c_60, plain, (![B_27, A_28]: (v1_relat_1(B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_28)) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.97/1.47  tff(c_63, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_60])).
% 2.97/1.47  tff(c_66, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_63])).
% 2.97/1.47  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.97/1.47  tff(c_67, plain, (![A_29]: ('#skF_2'(A_29)!='#skF_1'(A_29) | v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.47  tff(c_38, plain, ('#skF_7'!='#skF_6' | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.97/1.47  tff(c_57, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_38])).
% 2.97/1.47  tff(c_70, plain, ('#skF_2'('#skF_5')!='#skF_1'('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_67, c_57])).
% 2.97/1.47  tff(c_73, plain, ('#skF_2'('#skF_5')!='#skF_1'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_36, c_70])).
% 2.97/1.47  tff(c_30, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.97/1.47  tff(c_58, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_30])).
% 2.97/1.47  tff(c_34, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.97/1.47  tff(c_77, plain, (![A_33, B_34, C_35]: (k1_relset_1(A_33, B_34, C_35)=k1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.97/1.47  tff(c_81, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_77])).
% 2.97/1.47  tff(c_116, plain, (![B_45, A_46, C_47]: (k1_xboole_0=B_45 | k1_relset_1(A_46, B_45, C_47)=A_46 | ~v1_funct_2(C_47, A_46, B_45) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_46, B_45))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.97/1.47  tff(c_119, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_116])).
% 2.97/1.47  tff(c_122, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_81, c_119])).
% 2.97/1.47  tff(c_123, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_58, c_122])).
% 2.97/1.47  tff(c_14, plain, (![A_6]: (r2_hidden('#skF_1'(A_6), k1_relat_1(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.47  tff(c_128, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_3') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_123, c_14])).
% 2.97/1.47  tff(c_135, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_3') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_36, c_128])).
% 2.97/1.47  tff(c_136, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_57, c_135])).
% 2.97/1.47  tff(c_12, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), k1_relat_1(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.47  tff(c_131, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_3') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_123, c_12])).
% 2.97/1.47  tff(c_138, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_3') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_36, c_131])).
% 2.97/1.47  tff(c_139, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_57, c_138])).
% 2.97/1.47  tff(c_92, plain, (![A_38]: (k1_funct_1(A_38, '#skF_2'(A_38))=k1_funct_1(A_38, '#skF_1'(A_38)) | v2_funct_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.47  tff(c_56, plain, (![E_24, D_23]: (v2_funct_1('#skF_5') | E_24=D_23 | k1_funct_1('#skF_5', E_24)!=k1_funct_1('#skF_5', D_23) | ~r2_hidden(E_24, '#skF_3') | ~r2_hidden(D_23, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.97/1.47  tff(c_82, plain, (![E_24, D_23]: (E_24=D_23 | k1_funct_1('#skF_5', E_24)!=k1_funct_1('#skF_5', D_23) | ~r2_hidden(E_24, '#skF_3') | ~r2_hidden(D_23, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_57, c_56])).
% 2.97/1.47  tff(c_98, plain, (![D_23]: (D_23='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_23)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_3') | ~r2_hidden(D_23, '#skF_3') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_82])).
% 2.97/1.47  tff(c_107, plain, (![D_23]: (D_23='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_23)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_3') | ~r2_hidden(D_23, '#skF_3') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_36, c_98])).
% 2.97/1.47  tff(c_108, plain, (![D_23]: (D_23='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_23)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_3') | ~r2_hidden(D_23, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_57, c_107])).
% 2.97/1.47  tff(c_154, plain, (![D_23]: (D_23='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_23)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden(D_23, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_108])).
% 2.97/1.47  tff(c_157, plain, ('#skF_2'('#skF_5')='#skF_1'('#skF_5') | ~r2_hidden('#skF_1'('#skF_5'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_154])).
% 2.97/1.47  tff(c_159, plain, ('#skF_2'('#skF_5')='#skF_1'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_157])).
% 2.97/1.47  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_159])).
% 2.97/1.47  tff(c_163, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 2.97/1.47  tff(c_162, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.97/1.47  tff(c_168, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_162])).
% 2.97/1.47  tff(c_181, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_32])).
% 2.97/1.47  tff(c_182, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.97/1.47  tff(c_185, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_181, c_182])).
% 2.97/1.47  tff(c_188, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_185])).
% 2.97/1.47  tff(c_189, plain, (![A_55]: ('#skF_2'(A_55)!='#skF_1'(A_55) | v2_funct_1(A_55) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.47  tff(c_192, plain, ('#skF_2'('#skF_5')!='#skF_1'('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_189, c_57])).
% 2.97/1.47  tff(c_195, plain, ('#skF_2'('#skF_5')!='#skF_1'('#skF_5') | ~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_192])).
% 2.97/1.47  tff(c_197, plain, ('#skF_2'('#skF_5')!='#skF_1'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_195])).
% 2.97/1.47  tff(c_173, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_34])).
% 2.97/1.47  tff(c_207, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.97/1.47  tff(c_211, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_181, c_207])).
% 2.97/1.47  tff(c_26, plain, (![B_17, C_18]: (k1_relset_1(k1_xboole_0, B_17, C_18)=k1_xboole_0 | ~v1_funct_2(C_18, k1_xboole_0, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.97/1.47  tff(c_249, plain, (![B_67, C_68]: (k1_relset_1('#skF_4', B_67, C_68)='#skF_4' | ~v1_funct_2(C_68, '#skF_4', B_67) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_67))))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_163, c_163, c_163, c_26])).
% 2.97/1.47  tff(c_252, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_181, c_249])).
% 2.97/1.47  tff(c_255, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_211, c_252])).
% 2.97/1.47  tff(c_260, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_255, c_14])).
% 2.97/1.47  tff(c_267, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_36, c_260])).
% 2.97/1.47  tff(c_268, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_57, c_267])).
% 2.97/1.47  tff(c_263, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_255, c_12])).
% 2.97/1.47  tff(c_270, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_36, c_263])).
% 2.97/1.47  tff(c_271, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_57, c_270])).
% 2.97/1.47  tff(c_218, plain, (![A_64]: (k1_funct_1(A_64, '#skF_2'(A_64))=k1_funct_1(A_64, '#skF_1'(A_64)) | v2_funct_1(A_64) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.47  tff(c_199, plain, (![E_24, D_23]: (v2_funct_1('#skF_5') | E_24=D_23 | k1_funct_1('#skF_5', E_24)!=k1_funct_1('#skF_5', D_23) | ~r2_hidden(E_24, '#skF_4') | ~r2_hidden(D_23, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_168, c_56])).
% 2.97/1.47  tff(c_200, plain, (![E_24, D_23]: (E_24=D_23 | k1_funct_1('#skF_5', E_24)!=k1_funct_1('#skF_5', D_23) | ~r2_hidden(E_24, '#skF_4') | ~r2_hidden(D_23, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_57, c_199])).
% 2.97/1.47  tff(c_224, plain, (![D_23]: (D_23='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_23)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(D_23, '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_218, c_200])).
% 2.97/1.47  tff(c_233, plain, (![D_23]: (D_23='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_23)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(D_23, '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_36, c_224])).
% 2.97/1.47  tff(c_234, plain, (![D_23]: (D_23='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_23)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(D_23, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_57, c_233])).
% 2.97/1.47  tff(c_307, plain, (![D_23]: (D_23='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_23)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden(D_23, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_234])).
% 2.97/1.47  tff(c_310, plain, ('#skF_2'('#skF_5')='#skF_1'('#skF_5') | ~r2_hidden('#skF_1'('#skF_5'), '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_307])).
% 2.97/1.47  tff(c_312, plain, ('#skF_2'('#skF_5')='#skF_1'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_268, c_310])).
% 2.97/1.47  tff(c_314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_312])).
% 2.97/1.47  tff(c_315, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_38])).
% 2.97/1.47  tff(c_316, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 2.97/1.47  tff(c_44, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.97/1.47  tff(c_322, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_44])).
% 2.97/1.47  tff(c_323, plain, (![B_79, A_80]: (v1_relat_1(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.97/1.47  tff(c_326, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_323])).
% 2.97/1.47  tff(c_329, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_326])).
% 2.97/1.47  tff(c_317, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_30])).
% 2.97/1.47  tff(c_340, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.97/1.47  tff(c_344, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_340])).
% 2.97/1.47  tff(c_363, plain, (![B_95, A_96, C_97]: (k1_xboole_0=B_95 | k1_relset_1(A_96, B_95, C_97)=A_96 | ~v1_funct_2(C_97, A_96, B_95) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.97/1.47  tff(c_366, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_363])).
% 2.97/1.47  tff(c_369, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_344, c_366])).
% 2.97/1.47  tff(c_370, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_317, c_369])).
% 2.97/1.47  tff(c_42, plain, (r2_hidden('#skF_7', '#skF_3') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.97/1.47  tff(c_320, plain, (r2_hidden('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_42])).
% 2.97/1.47  tff(c_40, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.97/1.47  tff(c_331, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_40])).
% 2.97/1.47  tff(c_403, plain, (![C_101, B_102, A_103]: (C_101=B_102 | k1_funct_1(A_103, C_101)!=k1_funct_1(A_103, B_102) | ~r2_hidden(C_101, k1_relat_1(A_103)) | ~r2_hidden(B_102, k1_relat_1(A_103)) | ~v2_funct_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.47  tff(c_409, plain, (![B_102]: (B_102='#skF_7' | k1_funct_1('#skF_5', B_102)!=k1_funct_1('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~r2_hidden(B_102, k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_331, c_403])).
% 2.97/1.47  tff(c_416, plain, (![B_104]: (B_104='#skF_7' | k1_funct_1('#skF_5', B_104)!=k1_funct_1('#skF_5', '#skF_6') | ~r2_hidden(B_104, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_36, c_316, c_370, c_320, c_370, c_409])).
% 2.97/1.47  tff(c_419, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_322, c_416])).
% 2.97/1.47  tff(c_426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_315, c_419])).
% 2.97/1.47  tff(c_428, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 2.97/1.47  tff(c_427, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.97/1.47  tff(c_433, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_428, c_427])).
% 2.97/1.47  tff(c_445, plain, (r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_433, c_44])).
% 2.97/1.47  tff(c_448, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_32])).
% 2.97/1.47  tff(c_455, plain, (![B_107, A_108]: (v1_relat_1(B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(A_108)) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.97/1.47  tff(c_458, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_448, c_455])).
% 2.97/1.47  tff(c_461, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_458])).
% 2.97/1.47  tff(c_438, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_433, c_34])).
% 2.97/1.47  tff(c_467, plain, (![A_113, B_114, C_115]: (k1_relset_1(A_113, B_114, C_115)=k1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.97/1.47  tff(c_471, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_448, c_467])).
% 2.97/1.47  tff(c_496, plain, (![B_119, C_120]: (k1_relset_1('#skF_4', B_119, C_120)='#skF_4' | ~v1_funct_2(C_120, '#skF_4', B_119) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_119))))), inference(demodulation, [status(thm), theory('equality')], [c_428, c_428, c_428, c_428, c_26])).
% 2.97/1.47  tff(c_499, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_448, c_496])).
% 2.97/1.47  tff(c_502, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_438, c_471, c_499])).
% 2.97/1.47  tff(c_447, plain, (r2_hidden('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_433, c_42])).
% 2.97/1.47  tff(c_450, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_40])).
% 2.97/1.47  tff(c_556, plain, (![C_129, B_130, A_131]: (C_129=B_130 | k1_funct_1(A_131, C_129)!=k1_funct_1(A_131, B_130) | ~r2_hidden(C_129, k1_relat_1(A_131)) | ~r2_hidden(B_130, k1_relat_1(A_131)) | ~v2_funct_1(A_131) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.47  tff(c_562, plain, (![B_130]: (B_130='#skF_7' | k1_funct_1('#skF_5', B_130)!=k1_funct_1('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~r2_hidden(B_130, k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_450, c_556])).
% 2.97/1.47  tff(c_569, plain, (![B_132]: (B_132='#skF_7' | k1_funct_1('#skF_5', B_132)!=k1_funct_1('#skF_5', '#skF_6') | ~r2_hidden(B_132, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_461, c_36, c_316, c_502, c_447, c_502, c_562])).
% 2.97/1.47  tff(c_575, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_445, c_569])).
% 2.97/1.47  tff(c_583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_315, c_575])).
% 2.97/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.47  
% 2.97/1.47  Inference rules
% 2.97/1.47  ----------------------
% 2.97/1.47  #Ref     : 6
% 2.97/1.47  #Sup     : 96
% 2.97/1.47  #Fact    : 0
% 2.97/1.47  #Define  : 0
% 2.97/1.47  #Split   : 3
% 2.97/1.47  #Chain   : 0
% 2.97/1.47  #Close   : 0
% 2.97/1.47  
% 2.97/1.47  Ordering : KBO
% 2.97/1.47  
% 2.97/1.47  Simplification rules
% 2.97/1.47  ----------------------
% 2.97/1.47  #Subsume      : 14
% 2.97/1.47  #Demod        : 178
% 2.97/1.47  #Tautology    : 80
% 2.97/1.47  #SimpNegUnit  : 18
% 2.97/1.47  #BackRed      : 8
% 2.97/1.47  
% 2.97/1.47  #Partial instantiations: 0
% 2.97/1.47  #Strategies tried      : 1
% 2.97/1.47  
% 2.97/1.47  Timing (in seconds)
% 2.97/1.47  ----------------------
% 2.97/1.48  Preprocessing        : 0.34
% 2.97/1.48  Parsing              : 0.18
% 2.97/1.48  CNF conversion       : 0.02
% 2.97/1.48  Main loop            : 0.32
% 2.97/1.48  Inferencing          : 0.12
% 2.97/1.48  Reduction            : 0.10
% 2.97/1.48  Demodulation         : 0.07
% 2.97/1.48  BG Simplification    : 0.02
% 2.97/1.48  Subsumption          : 0.05
% 2.97/1.48  Abstraction          : 0.02
% 2.97/1.48  MUC search           : 0.00
% 2.97/1.48  Cooper               : 0.00
% 2.97/1.48  Total                : 0.71
% 2.97/1.48  Index Insertion      : 0.00
% 2.97/1.48  Index Deletion       : 0.00
% 2.97/1.48  Index Matching       : 0.00
% 2.97/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
