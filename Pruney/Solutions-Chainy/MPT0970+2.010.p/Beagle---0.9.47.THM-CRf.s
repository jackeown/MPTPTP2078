%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:20 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 150 expanded)
%              Number of leaves         :   34 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 388 expanded)
%              Number of equality atoms :   40 ( 122 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ! [C] :
            ~ ( r2_hidden(C,A)
              & ! [D] :
                  ~ ( r2_hidden(D,k1_relat_1(B))
                    & C = k1_funct_1(B,D) ) )
       => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_122,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_relset_1(A_54,B_55,C_56) = k2_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_126,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_122])).

tff(c_40,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_128,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_40])).

tff(c_87,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_91,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_87])).

tff(c_102,plain,(
    ! [C_46,B_47,A_48] :
      ( v5_relat_1(C_46,B_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_48,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_106,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_102])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_1'(A_6,B_7),A_6)
      | r1_tarski(A_6,k2_relat_1(B_7))
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_50,plain,(
    ! [D_31] :
      ( r2_hidden('#skF_5'(D_31),'#skF_2')
      | ~ r2_hidden(D_31,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_134,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_138,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_134])).

tff(c_169,plain,(
    ! [B_74,A_75,C_76] :
      ( k1_xboole_0 = B_74
      | k1_relset_1(A_75,B_74,C_76) = A_75
      | ~ v1_funct_2(C_76,A_75,B_74)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_172,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_169])).

tff(c_175,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_138,c_172])).

tff(c_176,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_48,plain,(
    ! [D_31] :
      ( k1_funct_1('#skF_4','#skF_5'(D_31)) = D_31
      | ~ r2_hidden(D_31,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_192,plain,(
    ! [B_80,D_81,A_82] :
      ( k1_funct_1(B_80,D_81) != '#skF_1'(A_82,B_80)
      | ~ r2_hidden(D_81,k1_relat_1(B_80))
      | r1_tarski(A_82,k2_relat_1(B_80))
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_194,plain,(
    ! [D_31,A_82] :
      ( D_31 != '#skF_1'(A_82,'#skF_4')
      | ~ r2_hidden('#skF_5'(D_31),k1_relat_1('#skF_4'))
      | r1_tarski(A_82,k2_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(D_31,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_192])).

tff(c_196,plain,(
    ! [D_31,A_82] :
      ( D_31 != '#skF_1'(A_82,'#skF_4')
      | ~ r2_hidden('#skF_5'(D_31),'#skF_2')
      | r1_tarski(A_82,k2_relat_1('#skF_4'))
      | ~ r2_hidden(D_31,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_46,c_176,c_194])).

tff(c_202,plain,(
    ! [A_85] :
      ( ~ r2_hidden('#skF_5'('#skF_1'(A_85,'#skF_4')),'#skF_2')
      | r1_tarski(A_85,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_85,'#skF_4'),'#skF_3') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_196])).

tff(c_207,plain,(
    ! [A_86] :
      ( r1_tarski(A_86,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_86,'#skF_4'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_202])).

tff(c_211,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_207])).

tff(c_214,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_46,c_211])).

tff(c_92,plain,(
    ! [B_43,A_44] :
      ( r1_tarski(k2_relat_1(B_43),A_44)
      | ~ v5_relat_1(B_43,A_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [B_43,A_44] :
      ( k2_relat_1(B_43) = A_44
      | ~ r1_tarski(A_44,k2_relat_1(B_43))
      | ~ v5_relat_1(B_43,A_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_217,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_214,c_100])).

tff(c_222,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_106,c_217])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_222])).

tff(c_225,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    ! [B_36,A_37] :
      ( B_36 = A_37
      | ~ r1_tarski(B_36,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_55])).

tff(c_255,plain,(
    ! [A_91] :
      ( A_91 = '#skF_3'
      | ~ r1_tarski(A_91,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_225,c_64])).

tff(c_273,plain,(
    ! [B_92] :
      ( k2_relat_1(B_92) = '#skF_3'
      | ~ v5_relat_1(B_92,'#skF_3')
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_12,c_255])).

tff(c_276,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_273])).

tff(c_279,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_276])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.29  
% 2.27/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.29  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.27/1.29  
% 2.27/1.29  %Foreground sorts:
% 2.27/1.29  
% 2.27/1.29  
% 2.27/1.29  %Background operators:
% 2.27/1.29  
% 2.27/1.29  
% 2.27/1.29  %Foreground operators:
% 2.27/1.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.27/1.29  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.27/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.27/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.27/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.27/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.27/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.27/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.27/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.27/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.29  
% 2.27/1.31  tff(f_110, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 2.27/1.31  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.27/1.31  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.27/1.31  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.27/1.31  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.27/1.31  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, k1_relat_1(B)) & (C = k1_funct_1(B, D)))))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_funct_1)).
% 2.27/1.31  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.27/1.31  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.27/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.27/1.31  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.27/1.31  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.27/1.31  tff(c_122, plain, (![A_54, B_55, C_56]: (k2_relset_1(A_54, B_55, C_56)=k2_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.27/1.31  tff(c_126, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_122])).
% 2.27/1.31  tff(c_40, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.27/1.31  tff(c_128, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_40])).
% 2.27/1.31  tff(c_87, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.27/1.31  tff(c_91, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_87])).
% 2.27/1.31  tff(c_102, plain, (![C_46, B_47, A_48]: (v5_relat_1(C_46, B_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_48, B_47))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.27/1.31  tff(c_106, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_102])).
% 2.27/1.31  tff(c_12, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.27/1.31  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.27/1.31  tff(c_16, plain, (![A_6, B_7]: (r2_hidden('#skF_1'(A_6, B_7), A_6) | r1_tarski(A_6, k2_relat_1(B_7)) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.31  tff(c_50, plain, (![D_31]: (r2_hidden('#skF_5'(D_31), '#skF_2') | ~r2_hidden(D_31, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.27/1.31  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.27/1.31  tff(c_134, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.27/1.31  tff(c_138, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_134])).
% 2.27/1.31  tff(c_169, plain, (![B_74, A_75, C_76]: (k1_xboole_0=B_74 | k1_relset_1(A_75, B_74, C_76)=A_75 | ~v1_funct_2(C_76, A_75, B_74) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.27/1.31  tff(c_172, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_169])).
% 2.27/1.31  tff(c_175, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_138, c_172])).
% 2.27/1.31  tff(c_176, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_175])).
% 2.27/1.31  tff(c_48, plain, (![D_31]: (k1_funct_1('#skF_4', '#skF_5'(D_31))=D_31 | ~r2_hidden(D_31, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.27/1.31  tff(c_192, plain, (![B_80, D_81, A_82]: (k1_funct_1(B_80, D_81)!='#skF_1'(A_82, B_80) | ~r2_hidden(D_81, k1_relat_1(B_80)) | r1_tarski(A_82, k2_relat_1(B_80)) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.31  tff(c_194, plain, (![D_31, A_82]: (D_31!='#skF_1'(A_82, '#skF_4') | ~r2_hidden('#skF_5'(D_31), k1_relat_1('#skF_4')) | r1_tarski(A_82, k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden(D_31, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_192])).
% 2.27/1.31  tff(c_196, plain, (![D_31, A_82]: (D_31!='#skF_1'(A_82, '#skF_4') | ~r2_hidden('#skF_5'(D_31), '#skF_2') | r1_tarski(A_82, k2_relat_1('#skF_4')) | ~r2_hidden(D_31, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_46, c_176, c_194])).
% 2.27/1.31  tff(c_202, plain, (![A_85]: (~r2_hidden('#skF_5'('#skF_1'(A_85, '#skF_4')), '#skF_2') | r1_tarski(A_85, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_85, '#skF_4'), '#skF_3'))), inference(reflexivity, [status(thm), theory('equality')], [c_196])).
% 2.27/1.31  tff(c_207, plain, (![A_86]: (r1_tarski(A_86, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_86, '#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_202])).
% 2.27/1.31  tff(c_211, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_207])).
% 2.27/1.31  tff(c_214, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_46, c_211])).
% 2.27/1.31  tff(c_92, plain, (![B_43, A_44]: (r1_tarski(k2_relat_1(B_43), A_44) | ~v5_relat_1(B_43, A_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.27/1.31  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.31  tff(c_100, plain, (![B_43, A_44]: (k2_relat_1(B_43)=A_44 | ~r1_tarski(A_44, k2_relat_1(B_43)) | ~v5_relat_1(B_43, A_44) | ~v1_relat_1(B_43))), inference(resolution, [status(thm)], [c_92, c_2])).
% 2.27/1.31  tff(c_217, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_214, c_100])).
% 2.27/1.31  tff(c_222, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_106, c_217])).
% 2.27/1.31  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_222])).
% 2.27/1.31  tff(c_225, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_175])).
% 2.27/1.31  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.31  tff(c_55, plain, (![B_36, A_37]: (B_36=A_37 | ~r1_tarski(B_36, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.31  tff(c_64, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_55])).
% 2.27/1.31  tff(c_255, plain, (![A_91]: (A_91='#skF_3' | ~r1_tarski(A_91, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_225, c_64])).
% 2.27/1.31  tff(c_273, plain, (![B_92]: (k2_relat_1(B_92)='#skF_3' | ~v5_relat_1(B_92, '#skF_3') | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_12, c_255])).
% 2.27/1.31  tff(c_276, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_273])).
% 2.27/1.31  tff(c_279, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_276])).
% 2.27/1.31  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_279])).
% 2.27/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.31  
% 2.27/1.31  Inference rules
% 2.27/1.31  ----------------------
% 2.27/1.31  #Ref     : 1
% 2.27/1.31  #Sup     : 43
% 2.27/1.31  #Fact    : 0
% 2.27/1.31  #Define  : 0
% 2.27/1.31  #Split   : 1
% 2.27/1.31  #Chain   : 0
% 2.27/1.31  #Close   : 0
% 2.27/1.31  
% 2.27/1.31  Ordering : KBO
% 2.27/1.31  
% 2.27/1.31  Simplification rules
% 2.27/1.31  ----------------------
% 2.27/1.31  #Subsume      : 4
% 2.27/1.31  #Demod        : 41
% 2.27/1.31  #Tautology    : 22
% 2.27/1.31  #SimpNegUnit  : 2
% 2.27/1.31  #BackRed      : 10
% 2.27/1.31  
% 2.27/1.31  #Partial instantiations: 0
% 2.27/1.31  #Strategies tried      : 1
% 2.27/1.31  
% 2.27/1.31  Timing (in seconds)
% 2.27/1.31  ----------------------
% 2.27/1.31  Preprocessing        : 0.33
% 2.27/1.31  Parsing              : 0.17
% 2.27/1.31  CNF conversion       : 0.02
% 2.27/1.31  Main loop            : 0.22
% 2.27/1.31  Inferencing          : 0.08
% 2.27/1.31  Reduction            : 0.07
% 2.27/1.31  Demodulation         : 0.05
% 2.27/1.31  BG Simplification    : 0.02
% 2.27/1.31  Subsumption          : 0.04
% 2.27/1.31  Abstraction          : 0.01
% 2.27/1.31  MUC search           : 0.00
% 2.27/1.31  Cooper               : 0.00
% 2.27/1.31  Total                : 0.58
% 2.27/1.31  Index Insertion      : 0.00
% 2.27/1.31  Index Deletion       : 0.00
% 2.27/1.31  Index Matching       : 0.00
% 2.27/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
