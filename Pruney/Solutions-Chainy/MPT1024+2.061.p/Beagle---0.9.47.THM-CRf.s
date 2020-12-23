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
% DateTime   : Thu Dec  3 10:16:30 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 157 expanded)
%              Number of leaves         :   32 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  139 ( 379 expanded)
%              Number of equality atoms :   16 (  40 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_16,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_45,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_45])).

tff(c_51,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_48])).

tff(c_24,plain,(
    ! [A_18,B_19,C_20] :
      ( r2_hidden('#skF_1'(A_18,B_19,C_20),k1_relat_1(C_20))
      | ~ r2_hidden(A_18,k9_relat_1(C_20,B_19))
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_732,plain,(
    ! [A_192,C_193] :
      ( r2_hidden(k4_tarski(A_192,k1_funct_1(C_193,A_192)),C_193)
      | ~ r2_hidden(A_192,k1_relat_1(C_193))
      | ~ v1_funct_1(C_193)
      | ~ v1_relat_1(C_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_132,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k7_relset_1(A_76,B_77,C_78,D_79) = k9_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_135,plain,(
    ! [D_79] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_79) = k9_relat_1('#skF_5',D_79) ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_36,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_136,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_36])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] :
      ( r2_hidden('#skF_1'(A_18,B_19,C_20),B_19)
      | ~ r2_hidden(A_18,k9_relat_1(C_20,B_19))
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_179,plain,(
    ! [A_95,C_96] :
      ( r2_hidden(k4_tarski(A_95,k1_funct_1(C_96,A_95)),C_96)
      | ~ r2_hidden(A_95,k1_relat_1(C_96))
      | ~ v1_funct_1(C_96)
      | ~ v1_relat_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,(
    ! [C_42,B_43,A_44] :
      ( ~ v1_xboole_0(C_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(C_42))
      | ~ r2_hidden(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55,plain,(
    ! [A_44] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_44,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_52])).

tff(c_62,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_63,plain,(
    ! [A_46,C_47,B_48] :
      ( m1_subset_1(A_46,C_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(C_47))
      | ~ r2_hidden(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,(
    ! [A_46] :
      ( m1_subset_1(A_46,k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_46,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_63])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ! [A_50,C_51,B_52,D_53] :
      ( r2_hidden(A_50,C_51)
      | ~ r2_hidden(k4_tarski(A_50,B_52),k2_zfmisc_1(C_51,D_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_146,plain,(
    ! [A_81,C_82,D_83,B_84] :
      ( r2_hidden(A_81,C_82)
      | v1_xboole_0(k2_zfmisc_1(C_82,D_83))
      | ~ m1_subset_1(k4_tarski(A_81,B_84),k2_zfmisc_1(C_82,D_83)) ) ),
    inference(resolution,[status(thm)],[c_8,c_68])).

tff(c_150,plain,(
    ! [A_81,B_84] :
      ( r2_hidden(A_81,'#skF_2')
      | v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(k4_tarski(A_81,B_84),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_66,c_146])).

tff(c_153,plain,(
    ! [A_81,B_84] :
      ( r2_hidden(A_81,'#skF_2')
      | ~ r2_hidden(k4_tarski(A_81,B_84),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_150])).

tff(c_187,plain,(
    ! [A_95] :
      ( r2_hidden(A_95,'#skF_2')
      | ~ r2_hidden(A_95,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_179,c_153])).

tff(c_227,plain,(
    ! [A_97] :
      ( r2_hidden(A_97,'#skF_2')
      | ~ r2_hidden(A_97,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_42,c_187])).

tff(c_235,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_1'(A_18,B_19,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_18,k9_relat_1('#skF_5',B_19))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_227])).

tff(c_253,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_1'(A_99,B_100,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_99,k9_relat_1('#skF_5',B_100)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_235])).

tff(c_34,plain,(
    ! [F_35] :
      ( k1_funct_1('#skF_5',F_35) != '#skF_6'
      | ~ r2_hidden(F_35,'#skF_4')
      | ~ r2_hidden(F_35,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_415,plain,(
    ! [A_117,B_118] :
      ( k1_funct_1('#skF_5','#skF_1'(A_117,B_118,'#skF_5')) != '#skF_6'
      | ~ r2_hidden('#skF_1'(A_117,B_118,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_117,k9_relat_1('#skF_5',B_118)) ) ),
    inference(resolution,[status(thm)],[c_253,c_34])).

tff(c_419,plain,(
    ! [A_18] :
      ( k1_funct_1('#skF_5','#skF_1'(A_18,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_18,k9_relat_1('#skF_5','#skF_4'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_415])).

tff(c_428,plain,(
    ! [A_121] :
      ( k1_funct_1('#skF_5','#skF_1'(A_121,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_121,k9_relat_1('#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_419])).

tff(c_450,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(resolution,[status(thm)],[c_136,c_428])).

tff(c_281,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_hidden(k4_tarski('#skF_1'(A_104,B_105,C_106),A_104),C_106)
      | ~ r2_hidden(A_104,k9_relat_1(C_106,B_105))
      | ~ v1_relat_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [C_26,A_24,B_25] :
      ( k1_funct_1(C_26,A_24) = B_25
      | ~ r2_hidden(k4_tarski(A_24,B_25),C_26)
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_596,plain,(
    ! [C_147,A_148,B_149] :
      ( k1_funct_1(C_147,'#skF_1'(A_148,B_149,C_147)) = A_148
      | ~ v1_funct_1(C_147)
      | ~ r2_hidden(A_148,k9_relat_1(C_147,B_149))
      | ~ v1_relat_1(C_147) ) ),
    inference(resolution,[status(thm)],[c_281,c_28])).

tff(c_607,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_136,c_596])).

tff(c_619,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_42,c_607])).

tff(c_621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_450,c_619])).

tff(c_622,plain,(
    ! [A_44] : ~ r2_hidden(A_44,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_758,plain,(
    ! [A_192] :
      ( ~ r2_hidden(A_192,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_732,c_622])).

tff(c_783,plain,(
    ! [A_194] : ~ r2_hidden(A_194,k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_42,c_758])).

tff(c_791,plain,(
    ! [A_18,B_19] :
      ( ~ r2_hidden(A_18,k9_relat_1('#skF_5',B_19))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_783])).

tff(c_803,plain,(
    ! [A_18,B_19] : ~ r2_hidden(A_18,k9_relat_1('#skF_5',B_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_791])).

tff(c_728,plain,(
    ! [A_188,B_189,C_190,D_191] :
      ( k7_relset_1(A_188,B_189,C_190,D_191) = k9_relat_1(C_190,D_191)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_731,plain,(
    ! [D_191] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_191) = k9_relat_1('#skF_5',D_191) ),
    inference(resolution,[status(thm)],[c_38,c_728])).

tff(c_823,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_36])).

tff(c_825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_803,c_823])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.41  
% 2.82/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.42  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.82/1.42  
% 2.82/1.42  %Foreground sorts:
% 2.82/1.42  
% 2.82/1.42  
% 2.82/1.42  %Background operators:
% 2.82/1.42  
% 2.82/1.42  
% 2.82/1.42  %Foreground operators:
% 2.82/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.82/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.82/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.82/1.42  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.82/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.82/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.82/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.82/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.82/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.82/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.42  
% 2.82/1.43  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.82/1.43  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 2.82/1.43  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.82/1.43  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.82/1.43  tff(f_80, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.82/1.43  tff(f_84, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.82/1.43  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.82/1.43  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.82/1.43  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.82/1.43  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.82/1.43  tff(c_16, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.82/1.43  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.82/1.43  tff(c_45, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.82/1.43  tff(c_48, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_45])).
% 2.82/1.43  tff(c_51, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_48])).
% 2.82/1.43  tff(c_24, plain, (![A_18, B_19, C_20]: (r2_hidden('#skF_1'(A_18, B_19, C_20), k1_relat_1(C_20)) | ~r2_hidden(A_18, k9_relat_1(C_20, B_19)) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.82/1.43  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.82/1.43  tff(c_732, plain, (![A_192, C_193]: (r2_hidden(k4_tarski(A_192, k1_funct_1(C_193, A_192)), C_193) | ~r2_hidden(A_192, k1_relat_1(C_193)) | ~v1_funct_1(C_193) | ~v1_relat_1(C_193))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.82/1.43  tff(c_132, plain, (![A_76, B_77, C_78, D_79]: (k7_relset_1(A_76, B_77, C_78, D_79)=k9_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.82/1.43  tff(c_135, plain, (![D_79]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_79)=k9_relat_1('#skF_5', D_79))), inference(resolution, [status(thm)], [c_38, c_132])).
% 2.82/1.43  tff(c_36, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.82/1.43  tff(c_136, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_36])).
% 2.82/1.43  tff(c_20, plain, (![A_18, B_19, C_20]: (r2_hidden('#skF_1'(A_18, B_19, C_20), B_19) | ~r2_hidden(A_18, k9_relat_1(C_20, B_19)) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.82/1.43  tff(c_179, plain, (![A_95, C_96]: (r2_hidden(k4_tarski(A_95, k1_funct_1(C_96, A_95)), C_96) | ~r2_hidden(A_95, k1_relat_1(C_96)) | ~v1_funct_1(C_96) | ~v1_relat_1(C_96))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.82/1.43  tff(c_52, plain, (![C_42, B_43, A_44]: (~v1_xboole_0(C_42) | ~m1_subset_1(B_43, k1_zfmisc_1(C_42)) | ~r2_hidden(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.82/1.43  tff(c_55, plain, (![A_44]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_44, '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_52])).
% 2.82/1.43  tff(c_62, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_55])).
% 2.82/1.43  tff(c_63, plain, (![A_46, C_47, B_48]: (m1_subset_1(A_46, C_47) | ~m1_subset_1(B_48, k1_zfmisc_1(C_47)) | ~r2_hidden(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.82/1.43  tff(c_66, plain, (![A_46]: (m1_subset_1(A_46, k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_46, '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_63])).
% 2.82/1.43  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.82/1.43  tff(c_68, plain, (![A_50, C_51, B_52, D_53]: (r2_hidden(A_50, C_51) | ~r2_hidden(k4_tarski(A_50, B_52), k2_zfmisc_1(C_51, D_53)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.43  tff(c_146, plain, (![A_81, C_82, D_83, B_84]: (r2_hidden(A_81, C_82) | v1_xboole_0(k2_zfmisc_1(C_82, D_83)) | ~m1_subset_1(k4_tarski(A_81, B_84), k2_zfmisc_1(C_82, D_83)))), inference(resolution, [status(thm)], [c_8, c_68])).
% 2.82/1.43  tff(c_150, plain, (![A_81, B_84]: (r2_hidden(A_81, '#skF_2') | v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(k4_tarski(A_81, B_84), '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_146])).
% 2.82/1.43  tff(c_153, plain, (![A_81, B_84]: (r2_hidden(A_81, '#skF_2') | ~r2_hidden(k4_tarski(A_81, B_84), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_150])).
% 2.82/1.43  tff(c_187, plain, (![A_95]: (r2_hidden(A_95, '#skF_2') | ~r2_hidden(A_95, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_179, c_153])).
% 2.82/1.43  tff(c_227, plain, (![A_97]: (r2_hidden(A_97, '#skF_2') | ~r2_hidden(A_97, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_42, c_187])).
% 2.82/1.43  tff(c_235, plain, (![A_18, B_19]: (r2_hidden('#skF_1'(A_18, B_19, '#skF_5'), '#skF_2') | ~r2_hidden(A_18, k9_relat_1('#skF_5', B_19)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_227])).
% 2.82/1.43  tff(c_253, plain, (![A_99, B_100]: (r2_hidden('#skF_1'(A_99, B_100, '#skF_5'), '#skF_2') | ~r2_hidden(A_99, k9_relat_1('#skF_5', B_100)))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_235])).
% 2.82/1.43  tff(c_34, plain, (![F_35]: (k1_funct_1('#skF_5', F_35)!='#skF_6' | ~r2_hidden(F_35, '#skF_4') | ~r2_hidden(F_35, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.82/1.43  tff(c_415, plain, (![A_117, B_118]: (k1_funct_1('#skF_5', '#skF_1'(A_117, B_118, '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'(A_117, B_118, '#skF_5'), '#skF_4') | ~r2_hidden(A_117, k9_relat_1('#skF_5', B_118)))), inference(resolution, [status(thm)], [c_253, c_34])).
% 2.82/1.43  tff(c_419, plain, (![A_18]: (k1_funct_1('#skF_5', '#skF_1'(A_18, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_18, k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_415])).
% 2.82/1.43  tff(c_428, plain, (![A_121]: (k1_funct_1('#skF_5', '#skF_1'(A_121, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_121, k9_relat_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_419])).
% 2.82/1.43  tff(c_450, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(resolution, [status(thm)], [c_136, c_428])).
% 2.82/1.43  tff(c_281, plain, (![A_104, B_105, C_106]: (r2_hidden(k4_tarski('#skF_1'(A_104, B_105, C_106), A_104), C_106) | ~r2_hidden(A_104, k9_relat_1(C_106, B_105)) | ~v1_relat_1(C_106))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.82/1.43  tff(c_28, plain, (![C_26, A_24, B_25]: (k1_funct_1(C_26, A_24)=B_25 | ~r2_hidden(k4_tarski(A_24, B_25), C_26) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.82/1.43  tff(c_596, plain, (![C_147, A_148, B_149]: (k1_funct_1(C_147, '#skF_1'(A_148, B_149, C_147))=A_148 | ~v1_funct_1(C_147) | ~r2_hidden(A_148, k9_relat_1(C_147, B_149)) | ~v1_relat_1(C_147))), inference(resolution, [status(thm)], [c_281, c_28])).
% 2.82/1.43  tff(c_607, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_136, c_596])).
% 2.82/1.43  tff(c_619, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_51, c_42, c_607])).
% 2.82/1.43  tff(c_621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_450, c_619])).
% 2.82/1.43  tff(c_622, plain, (![A_44]: (~r2_hidden(A_44, '#skF_5'))), inference(splitRight, [status(thm)], [c_55])).
% 2.82/1.43  tff(c_758, plain, (![A_192]: (~r2_hidden(A_192, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_732, c_622])).
% 2.82/1.43  tff(c_783, plain, (![A_194]: (~r2_hidden(A_194, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_42, c_758])).
% 2.82/1.43  tff(c_791, plain, (![A_18, B_19]: (~r2_hidden(A_18, k9_relat_1('#skF_5', B_19)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_783])).
% 2.82/1.43  tff(c_803, plain, (![A_18, B_19]: (~r2_hidden(A_18, k9_relat_1('#skF_5', B_19)))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_791])).
% 2.82/1.43  tff(c_728, plain, (![A_188, B_189, C_190, D_191]: (k7_relset_1(A_188, B_189, C_190, D_191)=k9_relat_1(C_190, D_191) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.82/1.43  tff(c_731, plain, (![D_191]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_191)=k9_relat_1('#skF_5', D_191))), inference(resolution, [status(thm)], [c_38, c_728])).
% 2.82/1.43  tff(c_823, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_36])).
% 2.82/1.43  tff(c_825, plain, $false, inference(negUnitSimplification, [status(thm)], [c_803, c_823])).
% 2.82/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.43  
% 2.82/1.43  Inference rules
% 2.82/1.43  ----------------------
% 2.82/1.43  #Ref     : 0
% 2.82/1.43  #Sup     : 149
% 2.82/1.43  #Fact    : 0
% 2.82/1.43  #Define  : 0
% 2.82/1.43  #Split   : 11
% 2.82/1.43  #Chain   : 0
% 2.82/1.43  #Close   : 0
% 2.82/1.43  
% 2.82/1.43  Ordering : KBO
% 2.82/1.43  
% 2.82/1.43  Simplification rules
% 2.82/1.43  ----------------------
% 2.82/1.43  #Subsume      : 5
% 2.82/1.43  #Demod        : 32
% 2.82/1.43  #Tautology    : 12
% 2.82/1.43  #SimpNegUnit  : 6
% 2.82/1.43  #BackRed      : 2
% 2.82/1.43  
% 2.82/1.43  #Partial instantiations: 0
% 2.82/1.43  #Strategies tried      : 1
% 2.82/1.43  
% 2.82/1.43  Timing (in seconds)
% 2.82/1.43  ----------------------
% 2.82/1.44  Preprocessing        : 0.31
% 2.82/1.44  Parsing              : 0.16
% 2.82/1.44  CNF conversion       : 0.02
% 2.82/1.44  Main loop            : 0.36
% 2.82/1.44  Inferencing          : 0.14
% 2.82/1.44  Reduction            : 0.10
% 2.82/1.44  Demodulation         : 0.07
% 2.82/1.44  BG Simplification    : 0.02
% 2.82/1.44  Subsumption          : 0.07
% 2.82/1.44  Abstraction          : 0.02
% 2.82/1.44  MUC search           : 0.00
% 2.82/1.44  Cooper               : 0.00
% 2.82/1.44  Total                : 0.71
% 2.82/1.44  Index Insertion      : 0.00
% 2.82/1.44  Index Deletion       : 0.00
% 2.82/1.44  Index Matching       : 0.00
% 2.82/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
