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
% DateTime   : Thu Dec  3 10:17:34 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 118 expanded)
%              Number of leaves         :   36 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  129 ( 290 expanded)
%              Number of equality atoms :   36 (  70 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
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

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_27,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_42,plain,(
    m1_subset_1('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_112,plain,(
    ! [C_54,B_55,A_56] :
      ( v5_relat_1(C_54,B_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_56,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_121,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_112])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( r2_hidden(B_5,A_4)
      | ~ m1_subset_1(B_5,A_4)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_87,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_96,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_87])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_122,plain,(
    ! [A_57,B_58,C_59] :
      ( k1_relset_1(A_57,B_58,C_59) = k1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_131,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_122])).

tff(c_174,plain,(
    ! [B_72,A_73,C_74] :
      ( k1_xboole_0 = B_72
      | k1_relset_1(A_73,B_72,C_74) = A_73
      | ~ v1_funct_2(C_74,A_73,B_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_181,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_174])).

tff(c_185,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_131,c_181])).

tff(c_186,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_196,plain,(
    ! [A_75,B_76,C_77] :
      ( k7_partfun1(A_75,B_76,C_77) = k1_funct_1(B_76,C_77)
      | ~ r2_hidden(C_77,k1_relat_1(B_76))
      | ~ v1_funct_1(B_76)
      | ~ v5_relat_1(B_76,A_75)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_198,plain,(
    ! [A_75,C_77] :
      ( k7_partfun1(A_75,'#skF_4',C_77) = k1_funct_1('#skF_4',C_77)
      | ~ r2_hidden(C_77,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_75)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_196])).

tff(c_205,plain,(
    ! [A_78,C_79] :
      ( k7_partfun1(A_78,'#skF_4',C_79) = k1_funct_1('#skF_4',C_79)
      | ~ r2_hidden(C_79,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_48,c_198])).

tff(c_208,plain,(
    ! [A_78,B_5] :
      ( k7_partfun1(A_78,'#skF_4',B_5) = k1_funct_1('#skF_4',B_5)
      | ~ v5_relat_1('#skF_4',A_78)
      | ~ m1_subset_1(B_5,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10,c_205])).

tff(c_226,plain,(
    ! [A_84,B_85] :
      ( k7_partfun1(A_84,'#skF_4',B_85) = k1_funct_1('#skF_4',B_85)
      | ~ v5_relat_1('#skF_4',A_84)
      | ~ m1_subset_1(B_85,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_208])).

tff(c_230,plain,(
    ! [B_86] :
      ( k7_partfun1('#skF_3','#skF_4',B_86) = k1_funct_1('#skF_4',B_86)
      | ~ m1_subset_1(B_86,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_121,c_226])).

tff(c_239,plain,(
    k7_partfun1('#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_230])).

tff(c_40,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k7_partfun1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_240,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_40])).

tff(c_212,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( k3_funct_2(A_80,B_81,C_82,D_83) = k1_funct_1(C_82,D_83)
      | ~ m1_subset_1(D_83,A_80)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_2(C_82,A_80,B_81)
      | ~ v1_funct_1(C_82)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_218,plain,(
    ! [B_81,C_82] :
      ( k3_funct_2('#skF_2',B_81,C_82,'#skF_5') = k1_funct_1(C_82,'#skF_5')
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_81)))
      | ~ v1_funct_2(C_82,'#skF_2',B_81)
      | ~ v1_funct_1(C_82)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_212])).

tff(c_245,plain,(
    ! [B_87,C_88] :
      ( k3_funct_2('#skF_2',B_87,C_88,'#skF_5') = k1_funct_1(C_88,'#skF_5')
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_87)))
      | ~ v1_funct_2(C_88,'#skF_2',B_87)
      | ~ v1_funct_1(C_88) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_218])).

tff(c_252,plain,
    ( k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_245])).

tff(c_256,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_252])).

tff(c_258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_256])).

tff(c_259,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [B_38,A_39] :
      ( ~ v1_xboole_0(k2_xboole_0(B_38,A_39))
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(A_3)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_62])).

tff(c_66,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_2,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_69,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2])).

tff(c_70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_267,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_70])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.28  
% 2.22/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.28  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.22/1.28  
% 2.22/1.28  %Foreground sorts:
% 2.22/1.28  
% 2.22/1.28  
% 2.22/1.28  %Background operators:
% 2.22/1.28  
% 2.22/1.28  
% 2.22/1.28  %Foreground operators:
% 2.22/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.22/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.28  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.22/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.22/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.22/1.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.22/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.22/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.22/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.22/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.28  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.22/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.28  
% 2.22/1.30  tff(f_124, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 2.22/1.30  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.22/1.30  tff(f_48, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.22/1.30  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.22/1.30  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.22/1.30  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.22/1.30  tff(f_91, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 2.22/1.30  tff(f_104, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.22/1.30  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.22/1.30  tff(f_33, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.22/1.30  tff(f_27, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.22/1.30  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.22/1.30  tff(c_42, plain, (m1_subset_1('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.22/1.30  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.22/1.30  tff(c_112, plain, (![C_54, B_55, A_56]: (v5_relat_1(C_54, B_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_56, B_55))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.22/1.30  tff(c_121, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_112])).
% 2.22/1.30  tff(c_52, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.22/1.30  tff(c_10, plain, (![B_5, A_4]: (r2_hidden(B_5, A_4) | ~m1_subset_1(B_5, A_4) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.22/1.30  tff(c_87, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.22/1.30  tff(c_96, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_87])).
% 2.22/1.30  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.22/1.30  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.22/1.30  tff(c_122, plain, (![A_57, B_58, C_59]: (k1_relset_1(A_57, B_58, C_59)=k1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.22/1.30  tff(c_131, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_122])).
% 2.22/1.30  tff(c_174, plain, (![B_72, A_73, C_74]: (k1_xboole_0=B_72 | k1_relset_1(A_73, B_72, C_74)=A_73 | ~v1_funct_2(C_74, A_73, B_72) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.30  tff(c_181, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_174])).
% 2.22/1.30  tff(c_185, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_131, c_181])).
% 2.22/1.30  tff(c_186, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_185])).
% 2.22/1.30  tff(c_196, plain, (![A_75, B_76, C_77]: (k7_partfun1(A_75, B_76, C_77)=k1_funct_1(B_76, C_77) | ~r2_hidden(C_77, k1_relat_1(B_76)) | ~v1_funct_1(B_76) | ~v5_relat_1(B_76, A_75) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.22/1.30  tff(c_198, plain, (![A_75, C_77]: (k7_partfun1(A_75, '#skF_4', C_77)=k1_funct_1('#skF_4', C_77) | ~r2_hidden(C_77, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_75) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_196])).
% 2.22/1.30  tff(c_205, plain, (![A_78, C_79]: (k7_partfun1(A_78, '#skF_4', C_79)=k1_funct_1('#skF_4', C_79) | ~r2_hidden(C_79, '#skF_2') | ~v5_relat_1('#skF_4', A_78))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_48, c_198])).
% 2.22/1.30  tff(c_208, plain, (![A_78, B_5]: (k7_partfun1(A_78, '#skF_4', B_5)=k1_funct_1('#skF_4', B_5) | ~v5_relat_1('#skF_4', A_78) | ~m1_subset_1(B_5, '#skF_2') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_205])).
% 2.22/1.30  tff(c_226, plain, (![A_84, B_85]: (k7_partfun1(A_84, '#skF_4', B_85)=k1_funct_1('#skF_4', B_85) | ~v5_relat_1('#skF_4', A_84) | ~m1_subset_1(B_85, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_208])).
% 2.22/1.30  tff(c_230, plain, (![B_86]: (k7_partfun1('#skF_3', '#skF_4', B_86)=k1_funct_1('#skF_4', B_86) | ~m1_subset_1(B_86, '#skF_2'))), inference(resolution, [status(thm)], [c_121, c_226])).
% 2.22/1.30  tff(c_239, plain, (k7_partfun1('#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_230])).
% 2.22/1.30  tff(c_40, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k7_partfun1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.22/1.30  tff(c_240, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_40])).
% 2.22/1.30  tff(c_212, plain, (![A_80, B_81, C_82, D_83]: (k3_funct_2(A_80, B_81, C_82, D_83)=k1_funct_1(C_82, D_83) | ~m1_subset_1(D_83, A_80) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_2(C_82, A_80, B_81) | ~v1_funct_1(C_82) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.22/1.30  tff(c_218, plain, (![B_81, C_82]: (k3_funct_2('#skF_2', B_81, C_82, '#skF_5')=k1_funct_1(C_82, '#skF_5') | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_81))) | ~v1_funct_2(C_82, '#skF_2', B_81) | ~v1_funct_1(C_82) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_212])).
% 2.22/1.30  tff(c_245, plain, (![B_87, C_88]: (k3_funct_2('#skF_2', B_87, C_88, '#skF_5')=k1_funct_1(C_88, '#skF_5') | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_87))) | ~v1_funct_2(C_88, '#skF_2', B_87) | ~v1_funct_1(C_88))), inference(negUnitSimplification, [status(thm)], [c_52, c_218])).
% 2.22/1.30  tff(c_252, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_245])).
% 2.22/1.30  tff(c_256, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_252])).
% 2.22/1.30  tff(c_258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_256])).
% 2.22/1.30  tff(c_259, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_185])).
% 2.22/1.30  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.30  tff(c_62, plain, (![B_38, A_39]: (~v1_xboole_0(k2_xboole_0(B_38, A_39)) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.30  tff(c_65, plain, (![A_3]: (~v1_xboole_0(A_3) | v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_62])).
% 2.22/1.30  tff(c_66, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitLeft, [status(thm)], [c_65])).
% 2.22/1.30  tff(c_2, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.22/1.30  tff(c_69, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_2])).
% 2.22/1.30  tff(c_70, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_65])).
% 2.22/1.30  tff(c_267, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_259, c_70])).
% 2.22/1.30  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_267])).
% 2.22/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.30  
% 2.22/1.30  Inference rules
% 2.22/1.30  ----------------------
% 2.22/1.30  #Ref     : 0
% 2.22/1.30  #Sup     : 42
% 2.22/1.30  #Fact    : 0
% 2.22/1.30  #Define  : 0
% 2.22/1.30  #Split   : 4
% 2.22/1.30  #Chain   : 0
% 2.22/1.30  #Close   : 0
% 2.22/1.30  
% 2.22/1.30  Ordering : KBO
% 2.22/1.30  
% 2.22/1.30  Simplification rules
% 2.22/1.30  ----------------------
% 2.22/1.30  #Subsume      : 16
% 2.22/1.30  #Demod        : 32
% 2.22/1.30  #Tautology    : 14
% 2.22/1.30  #SimpNegUnit  : 7
% 2.22/1.30  #BackRed      : 11
% 2.22/1.30  
% 2.22/1.30  #Partial instantiations: 0
% 2.22/1.30  #Strategies tried      : 1
% 2.22/1.30  
% 2.22/1.30  Timing (in seconds)
% 2.22/1.30  ----------------------
% 2.22/1.30  Preprocessing        : 0.33
% 2.22/1.30  Parsing              : 0.17
% 2.22/1.30  CNF conversion       : 0.02
% 2.22/1.30  Main loop            : 0.20
% 2.22/1.30  Inferencing          : 0.07
% 2.22/1.30  Reduction            : 0.06
% 2.22/1.30  Demodulation         : 0.04
% 2.22/1.30  BG Simplification    : 0.02
% 2.22/1.30  Subsumption          : 0.04
% 2.22/1.30  Abstraction          : 0.01
% 2.22/1.30  MUC search           : 0.00
% 2.22/1.30  Cooper               : 0.00
% 2.22/1.30  Total                : 0.57
% 2.22/1.30  Index Insertion      : 0.00
% 2.22/1.30  Index Deletion       : 0.00
% 2.22/1.30  Index Matching       : 0.00
% 2.22/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
