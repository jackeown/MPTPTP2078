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
% DateTime   : Thu Dec  3 10:15:47 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 391 expanded)
%              Number of leaves         :   31 ( 164 expanded)
%              Depth                    :   12
%              Number of atoms          :  142 (1412 expanded)
%              Number of equality atoms :   27 ( 316 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

tff(c_42,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_64,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_64])).

tff(c_70,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_67])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_50,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_5','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_71,plain,(
    ! [A_37,B_38,C_39] :
      ( k1_relset_1(A_37,B_38,C_39) = k1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_75,plain,(
    k1_relset_1('#skF_5','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_71])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k1_relset_1(A_40,A_40,B_41) = A_40
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k2_zfmisc_1(A_40,A_40)))
      | ~ v1_funct_2(B_41,A_40,A_40)
      | ~ v1_funct_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_83,plain,
    ( k1_relset_1('#skF_5','#skF_5','#skF_6') = '#skF_5'
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_80])).

tff(c_86,plain,(
    k1_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_75,c_83])).

tff(c_44,plain,(
    k1_funct_1('#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_101,plain,(
    ! [A_43,D_44] :
      ( r2_hidden(k1_funct_1(A_43,D_44),k2_relat_1(A_43))
      | ~ r2_hidden(D_44,k1_relat_1(A_43))
      | ~ v1_funct_1(k2_funct_1(A_43))
      | ~ v1_relat_1(k2_funct_1(A_43))
      | ~ v2_funct_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_104,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_8'),k2_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_101])).

tff(c_106,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_8'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_56,c_50,c_48,c_86,c_104])).

tff(c_107,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_110,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_107])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_56,c_110])).

tff(c_116,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_6,plain,(
    ! [A_6] :
      ( v1_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [A_7] :
      ( k1_relat_1(k2_funct_1(A_7)) = k2_relat_1(A_7)
      | ~ v1_funct_1(k2_funct_1(A_7))
      | ~ v1_relat_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_119,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_116,c_28])).

tff(c_122,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_56,c_50,c_119])).

tff(c_123,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_126,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_56,c_126])).

tff(c_132,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_46,plain,(
    r2_hidden('#skF_8','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_133,plain,(
    ! [A_45,D_46] :
      ( k1_funct_1(k2_funct_1(A_45),k1_funct_1(A_45,D_46)) = D_46
      | ~ r2_hidden(D_46,k1_relat_1(A_45))
      | ~ v1_funct_1(k2_funct_1(A_45))
      | ~ v1_relat_1(k2_funct_1(A_45))
      | ~ v2_funct_1(A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_151,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_8')) = '#skF_7'
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_133])).

tff(c_155,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_8')) = '#skF_7'
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_56,c_50,c_116,c_48,c_86,c_151])).

tff(c_163,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_155])).

tff(c_34,plain,(
    ! [A_7,D_23] :
      ( k1_funct_1(k2_funct_1(A_7),k1_funct_1(A_7,D_23)) = D_23
      | ~ r2_hidden(D_23,k1_relat_1(A_7))
      | ~ v1_funct_1(k2_funct_1(A_7))
      | ~ v1_relat_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_170,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_34])).

tff(c_182,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_56,c_50,c_116,c_132,c_46,c_86,c_170])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:15:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.23  
% 2.10/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.24  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.10/1.24  
% 2.10/1.24  %Foreground sorts:
% 2.10/1.24  
% 2.10/1.24  
% 2.10/1.24  %Background operators:
% 2.10/1.24  
% 2.10/1.24  
% 2.10/1.24  %Foreground operators:
% 2.10/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.10/1.24  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.10/1.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.10/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.24  tff('#skF_7', type, '#skF_7': $i).
% 2.10/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.10/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.10/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.10/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.10/1.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.10/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.10/1.24  tff('#skF_8', type, '#skF_8': $i).
% 2.10/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.10/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.10/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.24  
% 2.30/1.25  tff(f_104, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 2.30/1.25  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.30/1.25  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.30/1.25  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.30/1.25  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.30/1.25  tff(f_86, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 2.30/1.25  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 2.30/1.25  tff(c_42, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.25  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.30/1.25  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.25  tff(c_64, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.30/1.25  tff(c_67, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_64])).
% 2.30/1.25  tff(c_70, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_67])).
% 2.30/1.25  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.25  tff(c_50, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.25  tff(c_8, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.30/1.25  tff(c_48, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.25  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_5', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.25  tff(c_71, plain, (![A_37, B_38, C_39]: (k1_relset_1(A_37, B_38, C_39)=k1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.30/1.25  tff(c_75, plain, (k1_relset_1('#skF_5', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_71])).
% 2.30/1.25  tff(c_80, plain, (![A_40, B_41]: (k1_relset_1(A_40, A_40, B_41)=A_40 | ~m1_subset_1(B_41, k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))) | ~v1_funct_2(B_41, A_40, A_40) | ~v1_funct_1(B_41))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.30/1.25  tff(c_83, plain, (k1_relset_1('#skF_5', '#skF_5', '#skF_6')='#skF_5' | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_80])).
% 2.30/1.25  tff(c_86, plain, (k1_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_75, c_83])).
% 2.30/1.25  tff(c_44, plain, (k1_funct_1('#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.25  tff(c_101, plain, (![A_43, D_44]: (r2_hidden(k1_funct_1(A_43, D_44), k2_relat_1(A_43)) | ~r2_hidden(D_44, k1_relat_1(A_43)) | ~v1_funct_1(k2_funct_1(A_43)) | ~v1_relat_1(k2_funct_1(A_43)) | ~v2_funct_1(A_43) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.30/1.25  tff(c_104, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k2_relat_1('#skF_6')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_44, c_101])).
% 2.30/1.25  tff(c_106, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_56, c_50, c_48, c_86, c_104])).
% 2.30/1.25  tff(c_107, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_106])).
% 2.30/1.25  tff(c_110, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8, c_107])).
% 2.30/1.25  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_56, c_110])).
% 2.30/1.25  tff(c_116, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_106])).
% 2.30/1.25  tff(c_6, plain, (![A_6]: (v1_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.30/1.25  tff(c_28, plain, (![A_7]: (k1_relat_1(k2_funct_1(A_7))=k2_relat_1(A_7) | ~v1_funct_1(k2_funct_1(A_7)) | ~v1_relat_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.30/1.25  tff(c_119, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_116, c_28])).
% 2.30/1.25  tff(c_122, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_56, c_50, c_119])).
% 2.30/1.25  tff(c_123, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_122])).
% 2.30/1.25  tff(c_126, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_6, c_123])).
% 2.30/1.25  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_56, c_126])).
% 2.30/1.25  tff(c_132, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_122])).
% 2.30/1.25  tff(c_46, plain, (r2_hidden('#skF_8', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.25  tff(c_133, plain, (![A_45, D_46]: (k1_funct_1(k2_funct_1(A_45), k1_funct_1(A_45, D_46))=D_46 | ~r2_hidden(D_46, k1_relat_1(A_45)) | ~v1_funct_1(k2_funct_1(A_45)) | ~v1_relat_1(k2_funct_1(A_45)) | ~v2_funct_1(A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.30/1.25  tff(c_151, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_8'))='#skF_7' | ~r2_hidden('#skF_7', k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_44, c_133])).
% 2.30/1.25  tff(c_155, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_8'))='#skF_7' | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_56, c_50, c_116, c_48, c_86, c_151])).
% 2.30/1.25  tff(c_163, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_155])).
% 2.30/1.25  tff(c_34, plain, (![A_7, D_23]: (k1_funct_1(k2_funct_1(A_7), k1_funct_1(A_7, D_23))=D_23 | ~r2_hidden(D_23, k1_relat_1(A_7)) | ~v1_funct_1(k2_funct_1(A_7)) | ~v1_relat_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.30/1.25  tff(c_170, plain, ('#skF_7'='#skF_8' | ~r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_163, c_34])).
% 2.30/1.25  tff(c_182, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_56, c_50, c_116, c_132, c_46, c_86, c_170])).
% 2.30/1.25  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_182])).
% 2.30/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.25  
% 2.30/1.25  Inference rules
% 2.30/1.25  ----------------------
% 2.30/1.25  #Ref     : 0
% 2.30/1.25  #Sup     : 30
% 2.30/1.25  #Fact    : 0
% 2.30/1.25  #Define  : 0
% 2.30/1.25  #Split   : 2
% 2.30/1.25  #Chain   : 0
% 2.30/1.25  #Close   : 0
% 2.30/1.25  
% 2.30/1.25  Ordering : KBO
% 2.30/1.25  
% 2.30/1.25  Simplification rules
% 2.30/1.25  ----------------------
% 2.30/1.25  #Subsume      : 0
% 2.30/1.25  #Demod        : 36
% 2.30/1.25  #Tautology    : 13
% 2.30/1.25  #SimpNegUnit  : 1
% 2.30/1.25  #BackRed      : 1
% 2.30/1.25  
% 2.30/1.25  #Partial instantiations: 0
% 2.30/1.25  #Strategies tried      : 1
% 2.30/1.25  
% 2.30/1.25  Timing (in seconds)
% 2.30/1.25  ----------------------
% 2.30/1.25  Preprocessing        : 0.32
% 2.30/1.25  Parsing              : 0.16
% 2.30/1.25  CNF conversion       : 0.03
% 2.30/1.25  Main loop            : 0.17
% 2.30/1.26  Inferencing          : 0.05
% 2.30/1.26  Reduction            : 0.06
% 2.30/1.26  Demodulation         : 0.04
% 2.30/1.26  BG Simplification    : 0.02
% 2.30/1.26  Subsumption          : 0.04
% 2.30/1.26  Abstraction          : 0.01
% 2.30/1.26  MUC search           : 0.00
% 2.30/1.26  Cooper               : 0.00
% 2.30/1.26  Total                : 0.53
% 2.30/1.26  Index Insertion      : 0.00
% 2.30/1.26  Index Deletion       : 0.00
% 2.30/1.26  Index Matching       : 0.00
% 2.30/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
