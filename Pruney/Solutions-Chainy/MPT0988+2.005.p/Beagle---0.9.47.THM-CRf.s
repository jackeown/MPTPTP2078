%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:54 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 338 expanded)
%              Number of leaves         :   33 ( 141 expanded)
%              Depth                    :   17
%              Number of atoms          :  248 (2144 expanded)
%              Number of equality atoms :   86 ( 828 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_159,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & v2_funct_1(C)
                & ! [E,F] :
                    ( ( ( r2_hidden(E,B)
                        & k1_funct_1(D,E) = F )
                     => ( r2_hidden(F,A)
                        & k1_funct_1(C,F) = E ) )
                    & ( ( r2_hidden(F,A)
                        & k1_funct_1(C,F) = E )
                     => ( r2_hidden(E,B)
                        & k1_funct_1(D,E) = F ) ) ) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_73,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_73])).

tff(c_85,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_79])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_44,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_46,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_154,plain,(
    ! [A_51,B_52,C_53] :
      ( k2_relset_1(A_51,B_52,C_53) = k2_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_160,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_154])).

tff(c_163,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_160])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    k2_funct_1('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_272,plain,(
    ! [C_79,B_80,A_81] :
      ( m1_subset_1(k2_funct_1(C_79),k1_zfmisc_1(k2_zfmisc_1(B_80,A_81)))
      | k2_relset_1(A_81,B_80,C_79) != B_80
      | ~ v2_funct_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80)))
      | ~ v1_funct_2(C_79,A_81,B_80)
      | ~ v1_funct_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_305,plain,(
    ! [C_79,B_80,A_81] :
      ( v1_relat_1(k2_funct_1(C_79))
      | ~ v1_relat_1(k2_zfmisc_1(B_80,A_81))
      | k2_relset_1(A_81,B_80,C_79) != B_80
      | ~ v2_funct_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80)))
      | ~ v1_funct_2(C_79,A_81,B_80)
      | ~ v1_funct_1(C_79) ) ),
    inference(resolution,[status(thm)],[c_272,c_2])).

tff(c_318,plain,(
    ! [C_82,A_83,B_84] :
      ( v1_relat_1(k2_funct_1(C_82))
      | k2_relset_1(A_83,B_84,C_82) != B_84
      | ~ v2_funct_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_2(C_82,A_83,B_84)
      | ~ v1_funct_1(C_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_305])).

tff(c_327,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_318])).

tff(c_334,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_44,c_46,c_327])).

tff(c_239,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_funct_1(k2_funct_1(C_71))
      | k2_relset_1(A_72,B_73,C_71) != B_73
      | ~ v2_funct_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ v1_funct_2(C_71,A_72,B_73)
      | ~ v1_funct_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_245,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_239])).

tff(c_251,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_44,c_46,c_245])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_76,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_73])).

tff(c_82,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_76])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_137,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_144,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_137])).

tff(c_176,plain,(
    ! [B_61,A_62,C_63] :
      ( k1_xboole_0 = B_61
      | k1_relset_1(A_62,B_61,C_63) = A_62
      | ~ v1_funct_2(C_63,A_62,B_61)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_179,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_176])).

tff(c_185,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_144,c_179])).

tff(c_186,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_185])).

tff(c_223,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_1'(A_67,B_68),k1_relat_1(A_67))
      | B_68 = A_67
      | k1_relat_1(B_68) != k1_relat_1(A_67)
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_229,plain,(
    ! [B_68] :
      ( r2_hidden('#skF_1'('#skF_5',B_68),'#skF_3')
      | B_68 = '#skF_5'
      | k1_relat_1(B_68) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_223])).

tff(c_236,plain,(
    ! [B_68] :
      ( r2_hidden('#skF_1'('#skF_5',B_68),'#skF_3')
      | B_68 = '#skF_5'
      | k1_relat_1(B_68) != '#skF_3'
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_52,c_186,c_229])).

tff(c_60,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_4',k1_funct_1('#skF_5',E_36)) = E_36
      | ~ r2_hidden(E_36,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_62,plain,(
    ! [E_36] :
      ( r2_hidden(k1_funct_1('#skF_5',E_36),'#skF_2')
      | ~ r2_hidden(E_36,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_335,plain,(
    ! [D_85,C_86,B_87,A_88] :
      ( k1_funct_1(k2_funct_1(D_85),k1_funct_1(D_85,C_86)) = C_86
      | k1_xboole_0 = B_87
      | ~ r2_hidden(C_86,A_88)
      | ~ v2_funct_1(D_85)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87)))
      | ~ v1_funct_2(D_85,A_88,B_87)
      | ~ v1_funct_1(D_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_399,plain,(
    ! [D_97,E_98,B_99] :
      ( k1_funct_1(k2_funct_1(D_97),k1_funct_1(D_97,k1_funct_1('#skF_5',E_98))) = k1_funct_1('#skF_5',E_98)
      | k1_xboole_0 = B_99
      | ~ v2_funct_1(D_97)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_99)))
      | ~ v1_funct_2(D_97,'#skF_2',B_99)
      | ~ v1_funct_1(D_97)
      | ~ r2_hidden(E_98,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_62,c_335])).

tff(c_404,plain,(
    ! [E_98] :
      ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4',k1_funct_1('#skF_5',E_98))) = k1_funct_1('#skF_5',E_98)
      | k1_xboole_0 = '#skF_3'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ r2_hidden(E_98,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_399])).

tff(c_408,plain,(
    ! [E_98] :
      ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4',k1_funct_1('#skF_5',E_98))) = k1_funct_1('#skF_5',E_98)
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(E_98,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_44,c_404])).

tff(c_410,plain,(
    ! [E_100] :
      ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4',k1_funct_1('#skF_5',E_100))) = k1_funct_1('#skF_5',E_100)
      | ~ r2_hidden(E_100,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_408])).

tff(c_425,plain,(
    ! [E_101] :
      ( k1_funct_1(k2_funct_1('#skF_4'),E_101) = k1_funct_1('#skF_5',E_101)
      | ~ r2_hidden(E_101,'#skF_3')
      | ~ r2_hidden(E_101,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_410])).

tff(c_10,plain,(
    ! [B_11,A_7] :
      ( k1_funct_1(B_11,'#skF_1'(A_7,B_11)) != k1_funct_1(A_7,'#skF_1'(A_7,B_11))
      | B_11 = A_7
      | k1_relat_1(B_11) != k1_relat_1(A_7)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_435,plain,(
    ! [A_7] :
      ( k1_funct_1(A_7,'#skF_1'(A_7,k2_funct_1('#skF_4'))) != k1_funct_1('#skF_5','#skF_1'(A_7,k2_funct_1('#skF_4')))
      | k2_funct_1('#skF_4') = A_7
      | k1_relat_1(k2_funct_1('#skF_4')) != k1_relat_1(A_7)
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7)
      | ~ r2_hidden('#skF_1'(A_7,k2_funct_1('#skF_4')),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_7,k2_funct_1('#skF_4')),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_10])).

tff(c_448,plain,(
    ! [A_7] :
      ( k1_funct_1(A_7,'#skF_1'(A_7,k2_funct_1('#skF_4'))) != k1_funct_1('#skF_5','#skF_1'(A_7,k2_funct_1('#skF_4')))
      | k2_funct_1('#skF_4') = A_7
      | k1_relat_1(k2_funct_1('#skF_4')) != k1_relat_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7)
      | ~ r2_hidden('#skF_1'(A_7,k2_funct_1('#skF_4')),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_251,c_435])).

tff(c_711,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_5',k2_funct_1('#skF_4')),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_448])).

tff(c_713,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3'
    | ~ r2_hidden('#skF_1'('#skF_5',k2_funct_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_52,c_186,c_711])).

tff(c_714,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3'
    | ~ r2_hidden('#skF_1'('#skF_5',k2_funct_1('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_713])).

tff(c_723,plain,(
    ~ r2_hidden('#skF_1'('#skF_5',k2_funct_1('#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_714])).

tff(c_726,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3'
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_236,c_723])).

tff(c_729,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_251,c_726])).

tff(c_730,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_729])).

tff(c_733,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_730])).

tff(c_736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_58,c_44,c_163,c_733])).

tff(c_737,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_714])).

tff(c_741,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_737])).

tff(c_744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_58,c_44,c_163,c_741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:23:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.49  
% 3.25/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.49  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.25/1.49  
% 3.25/1.49  %Foreground sorts:
% 3.25/1.49  
% 3.25/1.49  
% 3.25/1.49  %Background operators:
% 3.25/1.49  
% 3.25/1.49  
% 3.25/1.49  %Foreground operators:
% 3.25/1.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.25/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.25/1.49  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.25/1.49  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.25/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.25/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.25/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.25/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.25/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.25/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.49  
% 3.25/1.51  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.25/1.51  tff(f_159, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) & (![E, F]: (((r2_hidden(E, B) & (k1_funct_1(D, E) = F)) => (r2_hidden(F, A) & (k1_funct_1(C, F) = E))) & ((r2_hidden(F, A) & (k1_funct_1(C, F) = E)) => (r2_hidden(E, B) & (k1_funct_1(D, E) = F)))))) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_2)).
% 3.25/1.51  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.25/1.51  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.25/1.51  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.25/1.51  tff(f_104, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.25/1.51  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.25/1.51  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.25/1.51  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 3.25/1.51  tff(f_118, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 3.25/1.51  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.25/1.51  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.25/1.51  tff(c_73, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.25/1.51  tff(c_79, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_73])).
% 3.25/1.51  tff(c_85, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_79])).
% 3.25/1.51  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.25/1.51  tff(c_44, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.25/1.51  tff(c_46, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.25/1.51  tff(c_154, plain, (![A_51, B_52, C_53]: (k2_relset_1(A_51, B_52, C_53)=k2_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.25/1.51  tff(c_160, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_154])).
% 3.25/1.51  tff(c_163, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_160])).
% 3.25/1.51  tff(c_8, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.25/1.51  tff(c_38, plain, (k2_funct_1('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.25/1.51  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.25/1.51  tff(c_272, plain, (![C_79, B_80, A_81]: (m1_subset_1(k2_funct_1(C_79), k1_zfmisc_1(k2_zfmisc_1(B_80, A_81))) | k2_relset_1(A_81, B_80, C_79)!=B_80 | ~v2_funct_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))) | ~v1_funct_2(C_79, A_81, B_80) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.25/1.51  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.25/1.51  tff(c_305, plain, (![C_79, B_80, A_81]: (v1_relat_1(k2_funct_1(C_79)) | ~v1_relat_1(k2_zfmisc_1(B_80, A_81)) | k2_relset_1(A_81, B_80, C_79)!=B_80 | ~v2_funct_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))) | ~v1_funct_2(C_79, A_81, B_80) | ~v1_funct_1(C_79))), inference(resolution, [status(thm)], [c_272, c_2])).
% 3.25/1.51  tff(c_318, plain, (![C_82, A_83, B_84]: (v1_relat_1(k2_funct_1(C_82)) | k2_relset_1(A_83, B_84, C_82)!=B_84 | ~v2_funct_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_2(C_82, A_83, B_84) | ~v1_funct_1(C_82))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_305])).
% 3.25/1.51  tff(c_327, plain, (v1_relat_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_318])).
% 3.25/1.51  tff(c_334, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_44, c_46, c_327])).
% 3.25/1.51  tff(c_239, plain, (![C_71, A_72, B_73]: (v1_funct_1(k2_funct_1(C_71)) | k2_relset_1(A_72, B_73, C_71)!=B_73 | ~v2_funct_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~v1_funct_2(C_71, A_72, B_73) | ~v1_funct_1(C_71))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.25/1.51  tff(c_245, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_239])).
% 3.25/1.51  tff(c_251, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_44, c_46, c_245])).
% 3.25/1.51  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.25/1.51  tff(c_76, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_73])).
% 3.25/1.51  tff(c_82, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_76])).
% 3.25/1.51  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.25/1.51  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.25/1.51  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.25/1.51  tff(c_137, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.25/1.51  tff(c_144, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_137])).
% 3.25/1.51  tff(c_176, plain, (![B_61, A_62, C_63]: (k1_xboole_0=B_61 | k1_relset_1(A_62, B_61, C_63)=A_62 | ~v1_funct_2(C_63, A_62, B_61) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.25/1.51  tff(c_179, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_176])).
% 3.25/1.51  tff(c_185, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_144, c_179])).
% 3.25/1.51  tff(c_186, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_42, c_185])).
% 3.25/1.51  tff(c_223, plain, (![A_67, B_68]: (r2_hidden('#skF_1'(A_67, B_68), k1_relat_1(A_67)) | B_68=A_67 | k1_relat_1(B_68)!=k1_relat_1(A_67) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.25/1.51  tff(c_229, plain, (![B_68]: (r2_hidden('#skF_1'('#skF_5', B_68), '#skF_3') | B_68='#skF_5' | k1_relat_1(B_68)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_68) | ~v1_relat_1(B_68) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_223])).
% 3.25/1.51  tff(c_236, plain, (![B_68]: (r2_hidden('#skF_1'('#skF_5', B_68), '#skF_3') | B_68='#skF_5' | k1_relat_1(B_68)!='#skF_3' | ~v1_funct_1(B_68) | ~v1_relat_1(B_68))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_52, c_186, c_229])).
% 3.25/1.51  tff(c_60, plain, (![E_36]: (k1_funct_1('#skF_4', k1_funct_1('#skF_5', E_36))=E_36 | ~r2_hidden(E_36, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.25/1.51  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.25/1.51  tff(c_62, plain, (![E_36]: (r2_hidden(k1_funct_1('#skF_5', E_36), '#skF_2') | ~r2_hidden(E_36, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.25/1.51  tff(c_335, plain, (![D_85, C_86, B_87, A_88]: (k1_funct_1(k2_funct_1(D_85), k1_funct_1(D_85, C_86))=C_86 | k1_xboole_0=B_87 | ~r2_hidden(C_86, A_88) | ~v2_funct_1(D_85) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))) | ~v1_funct_2(D_85, A_88, B_87) | ~v1_funct_1(D_85))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.25/1.51  tff(c_399, plain, (![D_97, E_98, B_99]: (k1_funct_1(k2_funct_1(D_97), k1_funct_1(D_97, k1_funct_1('#skF_5', E_98)))=k1_funct_1('#skF_5', E_98) | k1_xboole_0=B_99 | ~v2_funct_1(D_97) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_99))) | ~v1_funct_2(D_97, '#skF_2', B_99) | ~v1_funct_1(D_97) | ~r2_hidden(E_98, '#skF_3'))), inference(resolution, [status(thm)], [c_62, c_335])).
% 3.25/1.51  tff(c_404, plain, (![E_98]: (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', k1_funct_1('#skF_5', E_98)))=k1_funct_1('#skF_5', E_98) | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~r2_hidden(E_98, '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_399])).
% 3.25/1.51  tff(c_408, plain, (![E_98]: (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', k1_funct_1('#skF_5', E_98)))=k1_funct_1('#skF_5', E_98) | k1_xboole_0='#skF_3' | ~r2_hidden(E_98, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_44, c_404])).
% 3.25/1.51  tff(c_410, plain, (![E_100]: (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', k1_funct_1('#skF_5', E_100)))=k1_funct_1('#skF_5', E_100) | ~r2_hidden(E_100, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_408])).
% 3.25/1.51  tff(c_425, plain, (![E_101]: (k1_funct_1(k2_funct_1('#skF_4'), E_101)=k1_funct_1('#skF_5', E_101) | ~r2_hidden(E_101, '#skF_3') | ~r2_hidden(E_101, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_410])).
% 3.25/1.51  tff(c_10, plain, (![B_11, A_7]: (k1_funct_1(B_11, '#skF_1'(A_7, B_11))!=k1_funct_1(A_7, '#skF_1'(A_7, B_11)) | B_11=A_7 | k1_relat_1(B_11)!=k1_relat_1(A_7) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.25/1.51  tff(c_435, plain, (![A_7]: (k1_funct_1(A_7, '#skF_1'(A_7, k2_funct_1('#skF_4')))!=k1_funct_1('#skF_5', '#skF_1'(A_7, k2_funct_1('#skF_4'))) | k2_funct_1('#skF_4')=A_7 | k1_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1(A_7) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7) | ~r2_hidden('#skF_1'(A_7, k2_funct_1('#skF_4')), '#skF_3') | ~r2_hidden('#skF_1'(A_7, k2_funct_1('#skF_4')), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_425, c_10])).
% 3.25/1.51  tff(c_448, plain, (![A_7]: (k1_funct_1(A_7, '#skF_1'(A_7, k2_funct_1('#skF_4')))!=k1_funct_1('#skF_5', '#skF_1'(A_7, k2_funct_1('#skF_4'))) | k2_funct_1('#skF_4')=A_7 | k1_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7) | ~r2_hidden('#skF_1'(A_7, k2_funct_1('#skF_4')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_251, c_435])).
% 3.25/1.51  tff(c_711, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden('#skF_1'('#skF_5', k2_funct_1('#skF_4')), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_448])).
% 3.25/1.51  tff(c_713, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3' | ~r2_hidden('#skF_1'('#skF_5', k2_funct_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_52, c_186, c_711])).
% 3.25/1.51  tff(c_714, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3' | ~r2_hidden('#skF_1'('#skF_5', k2_funct_1('#skF_4')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_713])).
% 3.25/1.51  tff(c_723, plain, (~r2_hidden('#skF_1'('#skF_5', k2_funct_1('#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_714])).
% 3.25/1.51  tff(c_726, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3' | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_236, c_723])).
% 3.25/1.51  tff(c_729, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_334, c_251, c_726])).
% 3.25/1.51  tff(c_730, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_38, c_729])).
% 3.25/1.51  tff(c_733, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8, c_730])).
% 3.25/1.51  tff(c_736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_58, c_44, c_163, c_733])).
% 3.25/1.51  tff(c_737, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitRight, [status(thm)], [c_714])).
% 3.25/1.51  tff(c_741, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8, c_737])).
% 3.25/1.51  tff(c_744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_58, c_44, c_163, c_741])).
% 3.25/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.51  
% 3.25/1.51  Inference rules
% 3.25/1.51  ----------------------
% 3.25/1.51  #Ref     : 2
% 3.25/1.51  #Sup     : 165
% 3.25/1.51  #Fact    : 0
% 3.25/1.51  #Define  : 0
% 3.25/1.51  #Split   : 2
% 3.25/1.51  #Chain   : 0
% 3.25/1.51  #Close   : 0
% 3.25/1.51  
% 3.25/1.51  Ordering : KBO
% 3.25/1.51  
% 3.25/1.51  Simplification rules
% 3.25/1.51  ----------------------
% 3.25/1.51  #Subsume      : 33
% 3.25/1.51  #Demod        : 83
% 3.25/1.51  #Tautology    : 61
% 3.25/1.51  #SimpNegUnit  : 8
% 3.25/1.51  #BackRed      : 2
% 3.25/1.51  
% 3.25/1.51  #Partial instantiations: 0
% 3.25/1.51  #Strategies tried      : 1
% 3.25/1.51  
% 3.25/1.51  Timing (in seconds)
% 3.25/1.51  ----------------------
% 3.48/1.51  Preprocessing        : 0.35
% 3.48/1.51  Parsing              : 0.18
% 3.48/1.51  CNF conversion       : 0.02
% 3.48/1.51  Main loop            : 0.39
% 3.48/1.51  Inferencing          : 0.14
% 3.48/1.51  Reduction            : 0.12
% 3.48/1.51  Demodulation         : 0.08
% 3.48/1.51  BG Simplification    : 0.02
% 3.48/1.51  Subsumption          : 0.08
% 3.48/1.51  Abstraction          : 0.02
% 3.48/1.51  MUC search           : 0.00
% 3.48/1.51  Cooper               : 0.00
% 3.48/1.51  Total                : 0.77
% 3.48/1.51  Index Insertion      : 0.00
% 3.48/1.51  Index Deletion       : 0.00
% 3.48/1.51  Index Matching       : 0.00
% 3.48/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
