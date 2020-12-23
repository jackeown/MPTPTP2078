%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:38 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 107 expanded)
%              Number of leaves         :   31 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   98 ( 235 expanded)
%              Number of equality atoms :   17 (  35 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_117,plain,(
    ! [A_63,B_64,C_65,D_66] :
      ( k7_relset_1(A_63,B_64,C_65,D_66) = k9_relat_1(C_65,D_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_124,plain,(
    ! [D_66] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_66) = k9_relat_1('#skF_5',D_66) ),
    inference(resolution,[status(thm)],[c_32,c_117])).

tff(c_30,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_125,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_30])).

tff(c_6,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_41,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_38])).

tff(c_44,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_41])).

tff(c_141,plain,(
    ! [A_68,B_69,C_70] :
      ( r2_hidden('#skF_1'(A_68,B_69,C_70),k1_relat_1(C_70))
      | ~ r2_hidden(A_68,k9_relat_1(C_70,B_69))
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_51,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_relset_1(A_42,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_55,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_51])).

tff(c_67,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1(k1_relset_1(A_51,B_52,C_53),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_79,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_67])).

tff(c_84,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_79])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_2')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_145,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1('#skF_1'(A_68,B_69,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_68,k9_relat_1('#skF_5',B_69))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_141,c_91])).

tff(c_149,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1('#skF_1'(A_71,B_72,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_71,k9_relat_1('#skF_5',B_72)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_145])).

tff(c_157,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_125,c_149])).

tff(c_60,plain,(
    ! [A_45,B_46,C_47] :
      ( r2_hidden('#skF_1'(A_45,B_46,C_47),B_46)
      | ~ r2_hidden(A_45,k9_relat_1(C_47,B_46))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [F_32] :
      ( k1_funct_1('#skF_5',F_32) != '#skF_6'
      | ~ r2_hidden(F_32,'#skF_4')
      | ~ m1_subset_1(F_32,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_65,plain,(
    ! [A_45,C_47] :
      ( k1_funct_1('#skF_5','#skF_1'(A_45,'#skF_4',C_47)) != '#skF_6'
      | ~ m1_subset_1('#skF_1'(A_45,'#skF_4',C_47),'#skF_2')
      | ~ r2_hidden(A_45,k9_relat_1(C_47,'#skF_4'))
      | ~ v1_relat_1(C_47) ) ),
    inference(resolution,[status(thm)],[c_60,c_28])).

tff(c_137,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_125,c_65])).

tff(c_140,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_137])).

tff(c_160,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_140])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_162,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden(k4_tarski('#skF_1'(A_76,B_77,C_78),A_76),C_78)
      | ~ r2_hidden(A_76,k9_relat_1(C_78,B_77))
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [C_17,A_15,B_16] :
      ( k1_funct_1(C_17,A_15) = B_16
      | ~ r2_hidden(k4_tarski(A_15,B_16),C_17)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_254,plain,(
    ! [C_87,A_88,B_89] :
      ( k1_funct_1(C_87,'#skF_1'(A_88,B_89,C_87)) = A_88
      | ~ v1_funct_1(C_87)
      | ~ r2_hidden(A_88,k9_relat_1(C_87,B_89))
      | ~ v1_relat_1(C_87) ) ),
    inference(resolution,[status(thm)],[c_162,c_18])).

tff(c_262,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_125,c_254])).

tff(c_270,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_262])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:51:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.36  
% 2.34/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.36  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.34/1.36  
% 2.34/1.36  %Foreground sorts:
% 2.34/1.36  
% 2.34/1.36  
% 2.34/1.36  %Background operators:
% 2.34/1.36  
% 2.34/1.36  
% 2.34/1.36  %Foreground operators:
% 2.34/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.34/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.34/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.34/1.36  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.34/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.34/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.34/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.34/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.34/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.34/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.34/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.34/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.34/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.34/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.36  
% 2.34/1.37  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 2.34/1.37  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.34/1.37  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.34/1.37  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.34/1.37  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.34/1.37  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.34/1.37  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.34/1.37  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.34/1.37  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.34/1.37  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.34/1.37  tff(c_117, plain, (![A_63, B_64, C_65, D_66]: (k7_relset_1(A_63, B_64, C_65, D_66)=k9_relat_1(C_65, D_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.34/1.37  tff(c_124, plain, (![D_66]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_66)=k9_relat_1('#skF_5', D_66))), inference(resolution, [status(thm)], [c_32, c_117])).
% 2.34/1.37  tff(c_30, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.34/1.37  tff(c_125, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_30])).
% 2.34/1.37  tff(c_6, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.34/1.37  tff(c_38, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.34/1.37  tff(c_41, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_38])).
% 2.34/1.37  tff(c_44, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_41])).
% 2.34/1.37  tff(c_141, plain, (![A_68, B_69, C_70]: (r2_hidden('#skF_1'(A_68, B_69, C_70), k1_relat_1(C_70)) | ~r2_hidden(A_68, k9_relat_1(C_70, B_69)) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.37  tff(c_51, plain, (![A_42, B_43, C_44]: (k1_relset_1(A_42, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.34/1.37  tff(c_55, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_51])).
% 2.34/1.37  tff(c_67, plain, (![A_51, B_52, C_53]: (m1_subset_1(k1_relset_1(A_51, B_52, C_53), k1_zfmisc_1(A_51)) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.34/1.37  tff(c_79, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_55, c_67])).
% 2.34/1.37  tff(c_84, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_79])).
% 2.34/1.37  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.37  tff(c_91, plain, (![A_1]: (m1_subset_1(A_1, '#skF_2') | ~r2_hidden(A_1, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_84, c_2])).
% 2.34/1.37  tff(c_145, plain, (![A_68, B_69]: (m1_subset_1('#skF_1'(A_68, B_69, '#skF_5'), '#skF_2') | ~r2_hidden(A_68, k9_relat_1('#skF_5', B_69)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_141, c_91])).
% 2.34/1.37  tff(c_149, plain, (![A_71, B_72]: (m1_subset_1('#skF_1'(A_71, B_72, '#skF_5'), '#skF_2') | ~r2_hidden(A_71, k9_relat_1('#skF_5', B_72)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_145])).
% 2.34/1.37  tff(c_157, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_125, c_149])).
% 2.34/1.37  tff(c_60, plain, (![A_45, B_46, C_47]: (r2_hidden('#skF_1'(A_45, B_46, C_47), B_46) | ~r2_hidden(A_45, k9_relat_1(C_47, B_46)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.37  tff(c_28, plain, (![F_32]: (k1_funct_1('#skF_5', F_32)!='#skF_6' | ~r2_hidden(F_32, '#skF_4') | ~m1_subset_1(F_32, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.34/1.37  tff(c_65, plain, (![A_45, C_47]: (k1_funct_1('#skF_5', '#skF_1'(A_45, '#skF_4', C_47))!='#skF_6' | ~m1_subset_1('#skF_1'(A_45, '#skF_4', C_47), '#skF_2') | ~r2_hidden(A_45, k9_relat_1(C_47, '#skF_4')) | ~v1_relat_1(C_47))), inference(resolution, [status(thm)], [c_60, c_28])).
% 2.34/1.37  tff(c_137, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_125, c_65])).
% 2.34/1.37  tff(c_140, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_137])).
% 2.34/1.37  tff(c_160, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_140])).
% 2.34/1.37  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.34/1.37  tff(c_162, plain, (![A_76, B_77, C_78]: (r2_hidden(k4_tarski('#skF_1'(A_76, B_77, C_78), A_76), C_78) | ~r2_hidden(A_76, k9_relat_1(C_78, B_77)) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.37  tff(c_18, plain, (![C_17, A_15, B_16]: (k1_funct_1(C_17, A_15)=B_16 | ~r2_hidden(k4_tarski(A_15, B_16), C_17) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.34/1.37  tff(c_254, plain, (![C_87, A_88, B_89]: (k1_funct_1(C_87, '#skF_1'(A_88, B_89, C_87))=A_88 | ~v1_funct_1(C_87) | ~r2_hidden(A_88, k9_relat_1(C_87, B_89)) | ~v1_relat_1(C_87))), inference(resolution, [status(thm)], [c_162, c_18])).
% 2.34/1.37  tff(c_262, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_125, c_254])).
% 2.34/1.37  tff(c_270, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_262])).
% 2.34/1.37  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_270])).
% 2.34/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.37  
% 2.34/1.37  Inference rules
% 2.34/1.37  ----------------------
% 2.34/1.37  #Ref     : 0
% 2.34/1.37  #Sup     : 47
% 2.34/1.37  #Fact    : 0
% 2.34/1.37  #Define  : 0
% 2.34/1.37  #Split   : 1
% 2.34/1.37  #Chain   : 0
% 2.34/1.37  #Close   : 0
% 2.34/1.37  
% 2.34/1.37  Ordering : KBO
% 2.34/1.37  
% 2.34/1.37  Simplification rules
% 2.34/1.37  ----------------------
% 2.34/1.37  #Subsume      : 3
% 2.34/1.37  #Demod        : 10
% 2.34/1.37  #Tautology    : 6
% 2.34/1.37  #SimpNegUnit  : 1
% 2.34/1.37  #BackRed      : 1
% 2.34/1.37  
% 2.34/1.37  #Partial instantiations: 0
% 2.34/1.37  #Strategies tried      : 1
% 2.34/1.37  
% 2.34/1.37  Timing (in seconds)
% 2.34/1.37  ----------------------
% 2.34/1.38  Preprocessing        : 0.34
% 2.34/1.38  Parsing              : 0.18
% 2.34/1.38  CNF conversion       : 0.03
% 2.34/1.38  Main loop            : 0.21
% 2.34/1.38  Inferencing          : 0.08
% 2.34/1.38  Reduction            : 0.06
% 2.34/1.38  Demodulation         : 0.04
% 2.34/1.38  BG Simplification    : 0.02
% 2.34/1.38  Subsumption          : 0.04
% 2.34/1.38  Abstraction          : 0.02
% 2.34/1.38  MUC search           : 0.00
% 2.34/1.38  Cooper               : 0.00
% 2.34/1.38  Total                : 0.58
% 2.34/1.38  Index Insertion      : 0.00
% 2.34/1.38  Index Deletion       : 0.00
% 2.34/1.38  Index Matching       : 0.00
% 2.34/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
