%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:18 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 336 expanded)
%              Number of leaves         :   34 ( 127 expanded)
%              Depth                    :   12
%              Number of atoms          :  188 ( 970 expanded)
%              Number of equality atoms :   61 ( 224 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_101,plain,(
    ! [C_54,B_55,A_56] :
      ( v1_xboole_0(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(B_55,A_56)))
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_112,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_101])).

tff(c_115,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_422,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( r2_relset_1(A_104,B_105,C_106,C_106)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_437,plain,(
    ! [C_108] :
      ( r2_relset_1('#skF_2','#skF_3',C_108,C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_46,c_422])).

tff(c_445,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_437])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_72,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_84,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_72])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_156,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_171,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_156])).

tff(c_483,plain,(
    ! [B_115,A_116,C_117] :
      ( k1_xboole_0 = B_115
      | k1_relset_1(A_116,B_115,C_117) = A_116
      | ~ v1_funct_2(C_117,A_116,B_115)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_495,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_483])).

tff(c_506,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_171,c_495])).

tff(c_515,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_83,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_72])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_170,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_156])).

tff(c_492,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_483])).

tff(c_503,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_170,c_492])).

tff(c_509,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_503])).

tff(c_573,plain,(
    ! [A_125,B_126] :
      ( r2_hidden('#skF_1'(A_125,B_126),k1_relat_1(A_125))
      | B_126 = A_125
      | k1_relat_1(B_126) != k1_relat_1(A_125)
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_582,plain,(
    ! [B_126] :
      ( r2_hidden('#skF_1'('#skF_4',B_126),'#skF_2')
      | B_126 = '#skF_4'
      | k1_relat_1(B_126) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_573])).

tff(c_633,plain,(
    ! [B_138] :
      ( r2_hidden('#skF_1'('#skF_4',B_138),'#skF_2')
      | B_138 = '#skF_4'
      | k1_relat_1(B_138) != '#skF_2'
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_50,c_509,c_582])).

tff(c_6,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_51,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_88,plain,(
    ! [A_47,C_48,B_49] :
      ( m1_subset_1(A_47,C_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(C_48))
      | ~ r2_hidden(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_97,plain,(
    ! [A_47,A_4] :
      ( m1_subset_1(A_47,A_4)
      | ~ r2_hidden(A_47,A_4) ) ),
    inference(resolution,[status(thm)],[c_51,c_88])).

tff(c_643,plain,(
    ! [B_140] :
      ( m1_subset_1('#skF_1'('#skF_4',B_140),'#skF_2')
      | B_140 = '#skF_4'
      | k1_relat_1(B_140) != '#skF_2'
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140) ) ),
    inference(resolution,[status(thm)],[c_633,c_97])).

tff(c_38,plain,(
    ! [E_35] :
      ( k1_funct_1('#skF_5',E_35) = k1_funct_1('#skF_4',E_35)
      | ~ m1_subset_1(E_35,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_960,plain,(
    ! [B_159] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_159)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_159))
      | B_159 = '#skF_4'
      | k1_relat_1(B_159) != '#skF_2'
      | ~ v1_funct_1(B_159)
      | ~ v1_relat_1(B_159) ) ),
    inference(resolution,[status(thm)],[c_643,c_38])).

tff(c_12,plain,(
    ! [B_12,A_8] :
      ( k1_funct_1(B_12,'#skF_1'(A_8,B_12)) != k1_funct_1(A_8,'#skF_1'(A_8,B_12))
      | B_12 = A_8
      | k1_relat_1(B_12) != k1_relat_1(A_8)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_967,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_12])).

tff(c_974,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_44,c_515,c_83,c_50,c_515,c_509,c_967])).

tff(c_36,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_986,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_36])).

tff(c_996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_986])).

tff(c_997,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1022,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_2])).

tff(c_1024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_1022])).

tff(c_1025,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_503])).

tff(c_1050,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1025,c_2])).

tff(c_1052,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_1050])).

tff(c_1053,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_1147,plain,(
    ! [B_165,A_166] :
      ( v1_xboole_0(k2_zfmisc_1(B_165,A_166))
      | ~ v1_xboole_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_51,c_101])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1061,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_1053,c_4])).

tff(c_1156,plain,(
    ! [B_167,A_168] :
      ( k2_zfmisc_1(B_167,A_168) = '#skF_4'
      | ~ v1_xboole_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_1147,c_1061])).

tff(c_1162,plain,(
    ! [B_167] : k2_zfmisc_1(B_167,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1053,c_1156])).

tff(c_2193,plain,(
    ! [A_265,B_266,C_267,D_268] :
      ( r2_relset_1(A_265,B_266,C_267,C_267)
      | ~ m1_subset_1(D_268,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266)))
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2208,plain,(
    ! [A_269,B_270,C_271] :
      ( r2_relset_1(A_269,B_270,C_271,C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270))) ) ),
    inference(resolution,[status(thm)],[c_51,c_2193])).

tff(c_2223,plain,(
    ! [A_272,B_273] : r2_relset_1(A_272,B_273,k2_zfmisc_1(A_272,B_273),k2_zfmisc_1(A_272,B_273)) ),
    inference(resolution,[status(thm)],[c_51,c_2208])).

tff(c_2250,plain,(
    ! [B_167] : r2_relset_1(B_167,'#skF_4','#skF_4',k2_zfmisc_1(B_167,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1162,c_2223])).

tff(c_2254,plain,(
    ! [B_167] : r2_relset_1(B_167,'#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_2250])).

tff(c_62,plain,(
    ! [B_38,A_39] :
      ( ~ v1_xboole_0(B_38)
      | B_38 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_65,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_2,c_62])).

tff(c_1060,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1053,c_65])).

tff(c_1054,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_1067,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1054,c_65])).

tff(c_1078,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_1067])).

tff(c_113,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_101])).

tff(c_1093,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_1078,c_113])).

tff(c_1097,plain,(
    ! [A_161] :
      ( A_161 = '#skF_4'
      | ~ v1_xboole_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_1053,c_4])).

tff(c_1104,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1093,c_1097])).

tff(c_1084,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1078,c_36])).

tff(c_1128,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1104,c_1084])).

tff(c_2258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2254,c_1128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.73  
% 4.34/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.73  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.34/1.73  
% 4.34/1.73  %Foreground sorts:
% 4.34/1.73  
% 4.34/1.73  
% 4.34/1.73  %Background operators:
% 4.34/1.73  
% 4.34/1.73  
% 4.34/1.73  %Foreground operators:
% 4.34/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.34/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.34/1.73  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.34/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.34/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.34/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.34/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.34/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.34/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.34/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.34/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.34/1.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.34/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.34/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.34/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.34/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.34/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.34/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.34/1.73  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.34/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.34/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.34/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.34/1.73  
% 4.34/1.75  tff(f_122, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 4.34/1.75  tff(f_73, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.34/1.75  tff(f_83, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 4.34/1.75  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.34/1.75  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.34/1.75  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.34/1.75  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 4.34/1.75  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.34/1.75  tff(f_38, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.34/1.75  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.34/1.75  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.34/1.75  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.34/1.75  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.34/1.75  tff(c_101, plain, (![C_54, B_55, A_56]: (v1_xboole_0(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(B_55, A_56))) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.34/1.75  tff(c_112, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_101])).
% 4.34/1.75  tff(c_115, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_112])).
% 4.34/1.75  tff(c_422, plain, (![A_104, B_105, C_106, D_107]: (r2_relset_1(A_104, B_105, C_106, C_106) | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.34/1.75  tff(c_437, plain, (![C_108]: (r2_relset_1('#skF_2', '#skF_3', C_108, C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_46, c_422])).
% 4.34/1.75  tff(c_445, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_437])).
% 4.34/1.75  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.34/1.75  tff(c_72, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.34/1.75  tff(c_84, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_72])).
% 4.34/1.75  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.34/1.75  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.34/1.75  tff(c_156, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.34/1.75  tff(c_171, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_156])).
% 4.34/1.75  tff(c_483, plain, (![B_115, A_116, C_117]: (k1_xboole_0=B_115 | k1_relset_1(A_116, B_115, C_117)=A_116 | ~v1_funct_2(C_117, A_116, B_115) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.34/1.75  tff(c_495, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_483])).
% 4.34/1.75  tff(c_506, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_171, c_495])).
% 4.34/1.75  tff(c_515, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_506])).
% 4.34/1.75  tff(c_83, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_72])).
% 4.34/1.75  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.34/1.75  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.34/1.75  tff(c_170, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_156])).
% 4.34/1.75  tff(c_492, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_483])).
% 4.34/1.75  tff(c_503, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_170, c_492])).
% 4.34/1.75  tff(c_509, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_503])).
% 4.34/1.75  tff(c_573, plain, (![A_125, B_126]: (r2_hidden('#skF_1'(A_125, B_126), k1_relat_1(A_125)) | B_126=A_125 | k1_relat_1(B_126)!=k1_relat_1(A_125) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.34/1.75  tff(c_582, plain, (![B_126]: (r2_hidden('#skF_1'('#skF_4', B_126), '#skF_2') | B_126='#skF_4' | k1_relat_1(B_126)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_509, c_573])).
% 4.34/1.75  tff(c_633, plain, (![B_138]: (r2_hidden('#skF_1'('#skF_4', B_138), '#skF_2') | B_138='#skF_4' | k1_relat_1(B_138)!='#skF_2' | ~v1_funct_1(B_138) | ~v1_relat_1(B_138))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_50, c_509, c_582])).
% 4.34/1.75  tff(c_6, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.34/1.75  tff(c_8, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.34/1.75  tff(c_51, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 4.34/1.75  tff(c_88, plain, (![A_47, C_48, B_49]: (m1_subset_1(A_47, C_48) | ~m1_subset_1(B_49, k1_zfmisc_1(C_48)) | ~r2_hidden(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.34/1.75  tff(c_97, plain, (![A_47, A_4]: (m1_subset_1(A_47, A_4) | ~r2_hidden(A_47, A_4))), inference(resolution, [status(thm)], [c_51, c_88])).
% 4.34/1.75  tff(c_643, plain, (![B_140]: (m1_subset_1('#skF_1'('#skF_4', B_140), '#skF_2') | B_140='#skF_4' | k1_relat_1(B_140)!='#skF_2' | ~v1_funct_1(B_140) | ~v1_relat_1(B_140))), inference(resolution, [status(thm)], [c_633, c_97])).
% 4.34/1.75  tff(c_38, plain, (![E_35]: (k1_funct_1('#skF_5', E_35)=k1_funct_1('#skF_4', E_35) | ~m1_subset_1(E_35, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.34/1.75  tff(c_960, plain, (![B_159]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_159))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_159)) | B_159='#skF_4' | k1_relat_1(B_159)!='#skF_2' | ~v1_funct_1(B_159) | ~v1_relat_1(B_159))), inference(resolution, [status(thm)], [c_643, c_38])).
% 4.34/1.75  tff(c_12, plain, (![B_12, A_8]: (k1_funct_1(B_12, '#skF_1'(A_8, B_12))!=k1_funct_1(A_8, '#skF_1'(A_8, B_12)) | B_12=A_8 | k1_relat_1(B_12)!=k1_relat_1(A_8) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.34/1.75  tff(c_967, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_960, c_12])).
% 4.34/1.75  tff(c_974, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_44, c_515, c_83, c_50, c_515, c_509, c_967])).
% 4.34/1.75  tff(c_36, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.34/1.75  tff(c_986, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_974, c_36])).
% 4.34/1.75  tff(c_996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_445, c_986])).
% 4.34/1.75  tff(c_997, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_506])).
% 4.34/1.75  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.34/1.75  tff(c_1022, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_997, c_2])).
% 4.34/1.75  tff(c_1024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_1022])).
% 4.34/1.75  tff(c_1025, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_503])).
% 4.34/1.75  tff(c_1050, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1025, c_2])).
% 4.34/1.75  tff(c_1052, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_1050])).
% 4.34/1.75  tff(c_1053, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_112])).
% 4.34/1.75  tff(c_1147, plain, (![B_165, A_166]: (v1_xboole_0(k2_zfmisc_1(B_165, A_166)) | ~v1_xboole_0(A_166))), inference(resolution, [status(thm)], [c_51, c_101])).
% 4.34/1.75  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.34/1.75  tff(c_1061, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_1053, c_4])).
% 4.34/1.75  tff(c_1156, plain, (![B_167, A_168]: (k2_zfmisc_1(B_167, A_168)='#skF_4' | ~v1_xboole_0(A_168))), inference(resolution, [status(thm)], [c_1147, c_1061])).
% 4.34/1.75  tff(c_1162, plain, (![B_167]: (k2_zfmisc_1(B_167, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_1053, c_1156])).
% 4.34/1.75  tff(c_2193, plain, (![A_265, B_266, C_267, D_268]: (r2_relset_1(A_265, B_266, C_267, C_267) | ~m1_subset_1(D_268, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.34/1.75  tff(c_2208, plain, (![A_269, B_270, C_271]: (r2_relset_1(A_269, B_270, C_271, C_271) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))))), inference(resolution, [status(thm)], [c_51, c_2193])).
% 4.34/1.75  tff(c_2223, plain, (![A_272, B_273]: (r2_relset_1(A_272, B_273, k2_zfmisc_1(A_272, B_273), k2_zfmisc_1(A_272, B_273)))), inference(resolution, [status(thm)], [c_51, c_2208])).
% 4.34/1.75  tff(c_2250, plain, (![B_167]: (r2_relset_1(B_167, '#skF_4', '#skF_4', k2_zfmisc_1(B_167, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1162, c_2223])).
% 4.34/1.75  tff(c_2254, plain, (![B_167]: (r2_relset_1(B_167, '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1162, c_2250])).
% 4.34/1.75  tff(c_62, plain, (![B_38, A_39]: (~v1_xboole_0(B_38) | B_38=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.34/1.75  tff(c_65, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_2, c_62])).
% 4.34/1.75  tff(c_1060, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1053, c_65])).
% 4.34/1.75  tff(c_1054, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_112])).
% 4.34/1.75  tff(c_1067, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1054, c_65])).
% 4.34/1.75  tff(c_1078, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1060, c_1067])).
% 4.34/1.75  tff(c_113, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_101])).
% 4.34/1.75  tff(c_1093, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_1078, c_113])).
% 4.34/1.75  tff(c_1097, plain, (![A_161]: (A_161='#skF_4' | ~v1_xboole_0(A_161))), inference(resolution, [status(thm)], [c_1053, c_4])).
% 4.34/1.75  tff(c_1104, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_1093, c_1097])).
% 4.34/1.75  tff(c_1084, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1078, c_36])).
% 4.34/1.75  tff(c_1128, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1104, c_1084])).
% 4.34/1.75  tff(c_2258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2254, c_1128])).
% 4.34/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.75  
% 4.34/1.75  Inference rules
% 4.34/1.75  ----------------------
% 4.34/1.75  #Ref     : 1
% 4.34/1.75  #Sup     : 541
% 4.34/1.75  #Fact    : 0
% 4.34/1.75  #Define  : 0
% 4.34/1.75  #Split   : 7
% 4.34/1.75  #Chain   : 0
% 4.34/1.75  #Close   : 0
% 4.34/1.75  
% 4.34/1.75  Ordering : KBO
% 4.34/1.75  
% 4.34/1.75  Simplification rules
% 4.34/1.75  ----------------------
% 4.34/1.75  #Subsume      : 145
% 4.34/1.75  #Demod        : 440
% 4.34/1.75  #Tautology    : 166
% 4.34/1.75  #SimpNegUnit  : 13
% 4.34/1.75  #BackRed      : 79
% 4.34/1.75  
% 4.34/1.75  #Partial instantiations: 0
% 4.34/1.75  #Strategies tried      : 1
% 4.34/1.75  
% 4.34/1.75  Timing (in seconds)
% 4.34/1.75  ----------------------
% 4.34/1.76  Preprocessing        : 0.34
% 4.34/1.76  Parsing              : 0.18
% 4.34/1.76  CNF conversion       : 0.02
% 4.34/1.76  Main loop            : 0.63
% 4.34/1.76  Inferencing          : 0.21
% 4.34/1.76  Reduction            : 0.21
% 4.34/1.76  Demodulation         : 0.15
% 4.34/1.76  BG Simplification    : 0.03
% 4.34/1.76  Subsumption          : 0.14
% 4.34/1.76  Abstraction          : 0.03
% 4.34/1.76  MUC search           : 0.00
% 4.34/1.76  Cooper               : 0.00
% 4.34/1.76  Total                : 1.01
% 4.34/1.76  Index Insertion      : 0.00
% 4.34/1.76  Index Deletion       : 0.00
% 4.34/1.76  Index Matching       : 0.00
% 4.34/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
