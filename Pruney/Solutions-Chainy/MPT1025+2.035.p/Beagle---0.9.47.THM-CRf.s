%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:35 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 162 expanded)
%              Number of leaves         :   32 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 401 expanded)
%              Number of equality atoms :   16 (  53 expanded)
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

tff(f_102,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_41,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_53,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_57,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_22,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden('#skF_1'(A_15,B_16,C_17),k1_relat_1(C_17))
      | ~ r2_hidden(A_15,k9_relat_1(C_17,B_16))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1623,plain,(
    ! [A_315,C_316] :
      ( r2_hidden(k4_tarski(A_315,k1_funct_1(C_316,A_315)),C_316)
      | ~ r2_hidden(A_315,k1_relat_1(C_316))
      | ~ v1_funct_1(C_316)
      | ~ v1_relat_1(C_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_798,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( k7_relset_1(A_178,B_179,C_180,D_181) = k9_relat_1(C_180,D_181)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_801,plain,(
    ! [D_181] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_181) = k9_relat_1('#skF_5',D_181) ),
    inference(resolution,[status(thm)],[c_38,c_798])).

tff(c_36,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_803,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_801,c_36])).

tff(c_735,plain,(
    ! [A_156,B_157,C_158] :
      ( r2_hidden('#skF_1'(A_156,B_157,C_158),B_157)
      | ~ r2_hidden(A_156,k9_relat_1(C_158,B_157))
      | ~ v1_relat_1(C_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    ! [F_35] :
      ( k1_funct_1('#skF_5',F_35) != '#skF_6'
      | ~ r2_hidden(F_35,'#skF_4')
      | ~ m1_subset_1(F_35,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_743,plain,(
    ! [A_156,C_158] :
      ( k1_funct_1('#skF_5','#skF_1'(A_156,'#skF_4',C_158)) != '#skF_6'
      | ~ m1_subset_1('#skF_1'(A_156,'#skF_4',C_158),'#skF_2')
      | ~ r2_hidden(A_156,k9_relat_1(C_158,'#skF_4'))
      | ~ v1_relat_1(C_158) ) ),
    inference(resolution,[status(thm)],[c_735,c_34])).

tff(c_815,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_803,c_743])).

tff(c_823,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_815])).

tff(c_867,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_823])).

tff(c_917,plain,(
    ! [A_192,B_193,C_194] :
      ( r2_hidden(k4_tarski('#skF_1'(A_192,B_193,C_194),A_192),C_194)
      | ~ r2_hidden(A_192,k9_relat_1(C_194,B_193))
      | ~ v1_relat_1(C_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_64,plain,(
    ! [C_44,B_45,A_46] :
      ( ~ v1_xboole_0(C_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(C_44))
      | ~ r2_hidden(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_67,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_46,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_68,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_74,plain,(
    ! [A_51,C_52,B_53] :
      ( m1_subset_1(A_51,C_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(C_52))
      | ~ r2_hidden(A_51,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77,plain,(
    ! [A_51] :
      ( m1_subset_1(A_51,k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_51,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_74])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_69,plain,(
    ! [A_47,C_48,B_49,D_50] :
      ( r2_hidden(A_47,C_48)
      | ~ r2_hidden(k4_tarski(A_47,B_49),k2_zfmisc_1(C_48,D_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_868,plain,(
    ! [A_185,C_186,D_187,B_188] :
      ( r2_hidden(A_185,C_186)
      | v1_xboole_0(k2_zfmisc_1(C_186,D_187))
      | ~ m1_subset_1(k4_tarski(A_185,B_188),k2_zfmisc_1(C_186,D_187)) ) ),
    inference(resolution,[status(thm)],[c_10,c_69])).

tff(c_875,plain,(
    ! [A_185,B_188] :
      ( r2_hidden(A_185,'#skF_2')
      | v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(k4_tarski(A_185,B_188),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_77,c_868])).

tff(c_879,plain,(
    ! [A_185,B_188] :
      ( r2_hidden(A_185,'#skF_2')
      | ~ r2_hidden(k4_tarski(A_185,B_188),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_875])).

tff(c_925,plain,(
    ! [A_192,B_193] :
      ( r2_hidden('#skF_1'(A_192,B_193,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_192,k9_relat_1('#skF_5',B_193))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_917,c_879])).

tff(c_967,plain,(
    ! [A_195,B_196] :
      ( r2_hidden('#skF_1'(A_195,B_196,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_195,k9_relat_1('#skF_5',B_196)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_925])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_973,plain,(
    ! [A_199,B_200] :
      ( m1_subset_1('#skF_1'(A_199,B_200,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_199,k9_relat_1('#skF_5',B_200)) ) ),
    inference(resolution,[status(thm)],[c_967,c_8])).

tff(c_984,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_803,c_973])).

tff(c_998,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_867,c_984])).

tff(c_999,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_823])).

tff(c_1025,plain,(
    ! [A_207,B_208,C_209] :
      ( r2_hidden(k4_tarski('#skF_1'(A_207,B_208,C_209),A_207),C_209)
      | ~ r2_hidden(A_207,k9_relat_1(C_209,B_208))
      | ~ v1_relat_1(C_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [C_23,A_21,B_22] :
      ( k1_funct_1(C_23,A_21) = B_22
      | ~ r2_hidden(k4_tarski(A_21,B_22),C_23)
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1437,plain,(
    ! [C_255,A_256,B_257] :
      ( k1_funct_1(C_255,'#skF_1'(A_256,B_257,C_255)) = A_256
      | ~ v1_funct_1(C_255)
      | ~ r2_hidden(A_256,k9_relat_1(C_255,B_257))
      | ~ v1_relat_1(C_255) ) ),
    inference(resolution,[status(thm)],[c_1025,c_26])).

tff(c_1447,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_803,c_1437])).

tff(c_1459,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_42,c_1447])).

tff(c_1461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_999,c_1459])).

tff(c_1462,plain,(
    ! [A_46] : ~ r2_hidden(A_46,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_1656,plain,(
    ! [A_315] :
      ( ~ r2_hidden(A_315,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1623,c_1462])).

tff(c_1678,plain,(
    ! [A_317] : ~ r2_hidden(A_317,k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_42,c_1656])).

tff(c_1686,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden(A_15,k9_relat_1('#skF_5',B_16))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_1678])).

tff(c_1698,plain,(
    ! [A_15,B_16] : ~ r2_hidden(A_15,k9_relat_1('#skF_5',B_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1686])).

tff(c_1580,plain,(
    ! [A_301,B_302,C_303,D_304] :
      ( k7_relset_1(A_301,B_302,C_303,D_304) = k9_relat_1(C_303,D_304)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1583,plain,(
    ! [D_304] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_304) = k9_relat_1('#skF_5',D_304) ),
    inference(resolution,[status(thm)],[c_38,c_1580])).

tff(c_1585,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1583,c_36])).

tff(c_1702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1698,c_1585])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:11:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.59  
% 3.49/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.59  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.49/1.59  
% 3.49/1.59  %Foreground sorts:
% 3.49/1.59  
% 3.49/1.59  
% 3.49/1.59  %Background operators:
% 3.49/1.59  
% 3.49/1.59  
% 3.49/1.59  %Foreground operators:
% 3.49/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.49/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.49/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.49/1.59  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.49/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.49/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.49/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.59  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.49/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.49/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.49/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.49/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.59  
% 3.74/1.61  tff(f_102, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 3.74/1.61  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.74/1.61  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.74/1.61  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.74/1.61  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.74/1.61  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.74/1.61  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.74/1.61  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.74/1.61  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.74/1.61  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.74/1.61  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.74/1.61  tff(c_53, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.74/1.61  tff(c_57, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_53])).
% 3.74/1.61  tff(c_22, plain, (![A_15, B_16, C_17]: (r2_hidden('#skF_1'(A_15, B_16, C_17), k1_relat_1(C_17)) | ~r2_hidden(A_15, k9_relat_1(C_17, B_16)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.74/1.61  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.74/1.61  tff(c_1623, plain, (![A_315, C_316]: (r2_hidden(k4_tarski(A_315, k1_funct_1(C_316, A_315)), C_316) | ~r2_hidden(A_315, k1_relat_1(C_316)) | ~v1_funct_1(C_316) | ~v1_relat_1(C_316))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.74/1.61  tff(c_798, plain, (![A_178, B_179, C_180, D_181]: (k7_relset_1(A_178, B_179, C_180, D_181)=k9_relat_1(C_180, D_181) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.74/1.61  tff(c_801, plain, (![D_181]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_181)=k9_relat_1('#skF_5', D_181))), inference(resolution, [status(thm)], [c_38, c_798])).
% 3.74/1.61  tff(c_36, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.74/1.61  tff(c_803, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_801, c_36])).
% 3.74/1.61  tff(c_735, plain, (![A_156, B_157, C_158]: (r2_hidden('#skF_1'(A_156, B_157, C_158), B_157) | ~r2_hidden(A_156, k9_relat_1(C_158, B_157)) | ~v1_relat_1(C_158))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.74/1.61  tff(c_34, plain, (![F_35]: (k1_funct_1('#skF_5', F_35)!='#skF_6' | ~r2_hidden(F_35, '#skF_4') | ~m1_subset_1(F_35, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.74/1.61  tff(c_743, plain, (![A_156, C_158]: (k1_funct_1('#skF_5', '#skF_1'(A_156, '#skF_4', C_158))!='#skF_6' | ~m1_subset_1('#skF_1'(A_156, '#skF_4', C_158), '#skF_2') | ~r2_hidden(A_156, k9_relat_1(C_158, '#skF_4')) | ~v1_relat_1(C_158))), inference(resolution, [status(thm)], [c_735, c_34])).
% 3.74/1.61  tff(c_815, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_803, c_743])).
% 3.74/1.61  tff(c_823, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_815])).
% 3.74/1.61  tff(c_867, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_823])).
% 3.74/1.61  tff(c_917, plain, (![A_192, B_193, C_194]: (r2_hidden(k4_tarski('#skF_1'(A_192, B_193, C_194), A_192), C_194) | ~r2_hidden(A_192, k9_relat_1(C_194, B_193)) | ~v1_relat_1(C_194))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.74/1.61  tff(c_64, plain, (![C_44, B_45, A_46]: (~v1_xboole_0(C_44) | ~m1_subset_1(B_45, k1_zfmisc_1(C_44)) | ~r2_hidden(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.74/1.61  tff(c_67, plain, (![A_46]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_46, '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_64])).
% 3.74/1.61  tff(c_68, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_67])).
% 3.74/1.61  tff(c_74, plain, (![A_51, C_52, B_53]: (m1_subset_1(A_51, C_52) | ~m1_subset_1(B_53, k1_zfmisc_1(C_52)) | ~r2_hidden(A_51, B_53))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.74/1.61  tff(c_77, plain, (![A_51]: (m1_subset_1(A_51, k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_51, '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_74])).
% 3.74/1.61  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.74/1.61  tff(c_69, plain, (![A_47, C_48, B_49, D_50]: (r2_hidden(A_47, C_48) | ~r2_hidden(k4_tarski(A_47, B_49), k2_zfmisc_1(C_48, D_50)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.74/1.61  tff(c_868, plain, (![A_185, C_186, D_187, B_188]: (r2_hidden(A_185, C_186) | v1_xboole_0(k2_zfmisc_1(C_186, D_187)) | ~m1_subset_1(k4_tarski(A_185, B_188), k2_zfmisc_1(C_186, D_187)))), inference(resolution, [status(thm)], [c_10, c_69])).
% 3.74/1.61  tff(c_875, plain, (![A_185, B_188]: (r2_hidden(A_185, '#skF_2') | v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(k4_tarski(A_185, B_188), '#skF_5'))), inference(resolution, [status(thm)], [c_77, c_868])).
% 3.74/1.61  tff(c_879, plain, (![A_185, B_188]: (r2_hidden(A_185, '#skF_2') | ~r2_hidden(k4_tarski(A_185, B_188), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_875])).
% 3.74/1.61  tff(c_925, plain, (![A_192, B_193]: (r2_hidden('#skF_1'(A_192, B_193, '#skF_5'), '#skF_2') | ~r2_hidden(A_192, k9_relat_1('#skF_5', B_193)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_917, c_879])).
% 3.74/1.61  tff(c_967, plain, (![A_195, B_196]: (r2_hidden('#skF_1'(A_195, B_196, '#skF_5'), '#skF_2') | ~r2_hidden(A_195, k9_relat_1('#skF_5', B_196)))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_925])).
% 3.74/1.61  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.74/1.61  tff(c_973, plain, (![A_199, B_200]: (m1_subset_1('#skF_1'(A_199, B_200, '#skF_5'), '#skF_2') | ~r2_hidden(A_199, k9_relat_1('#skF_5', B_200)))), inference(resolution, [status(thm)], [c_967, c_8])).
% 3.74/1.61  tff(c_984, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_803, c_973])).
% 3.74/1.61  tff(c_998, plain, $false, inference(negUnitSimplification, [status(thm)], [c_867, c_984])).
% 3.74/1.61  tff(c_999, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(splitRight, [status(thm)], [c_823])).
% 3.74/1.61  tff(c_1025, plain, (![A_207, B_208, C_209]: (r2_hidden(k4_tarski('#skF_1'(A_207, B_208, C_209), A_207), C_209) | ~r2_hidden(A_207, k9_relat_1(C_209, B_208)) | ~v1_relat_1(C_209))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.74/1.61  tff(c_26, plain, (![C_23, A_21, B_22]: (k1_funct_1(C_23, A_21)=B_22 | ~r2_hidden(k4_tarski(A_21, B_22), C_23) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.74/1.61  tff(c_1437, plain, (![C_255, A_256, B_257]: (k1_funct_1(C_255, '#skF_1'(A_256, B_257, C_255))=A_256 | ~v1_funct_1(C_255) | ~r2_hidden(A_256, k9_relat_1(C_255, B_257)) | ~v1_relat_1(C_255))), inference(resolution, [status(thm)], [c_1025, c_26])).
% 3.74/1.61  tff(c_1447, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_803, c_1437])).
% 3.74/1.61  tff(c_1459, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_42, c_1447])).
% 3.74/1.61  tff(c_1461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_999, c_1459])).
% 3.74/1.61  tff(c_1462, plain, (![A_46]: (~r2_hidden(A_46, '#skF_5'))), inference(splitRight, [status(thm)], [c_67])).
% 3.74/1.61  tff(c_1656, plain, (![A_315]: (~r2_hidden(A_315, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1623, c_1462])).
% 3.74/1.61  tff(c_1678, plain, (![A_317]: (~r2_hidden(A_317, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_42, c_1656])).
% 3.74/1.61  tff(c_1686, plain, (![A_15, B_16]: (~r2_hidden(A_15, k9_relat_1('#skF_5', B_16)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_22, c_1678])).
% 3.74/1.61  tff(c_1698, plain, (![A_15, B_16]: (~r2_hidden(A_15, k9_relat_1('#skF_5', B_16)))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_1686])).
% 3.74/1.61  tff(c_1580, plain, (![A_301, B_302, C_303, D_304]: (k7_relset_1(A_301, B_302, C_303, D_304)=k9_relat_1(C_303, D_304) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.74/1.61  tff(c_1583, plain, (![D_304]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_304)=k9_relat_1('#skF_5', D_304))), inference(resolution, [status(thm)], [c_38, c_1580])).
% 3.74/1.61  tff(c_1585, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1583, c_36])).
% 3.74/1.61  tff(c_1702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1698, c_1585])).
% 3.74/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.61  
% 3.74/1.61  Inference rules
% 3.74/1.61  ----------------------
% 3.74/1.61  #Ref     : 0
% 3.74/1.61  #Sup     : 329
% 3.74/1.61  #Fact    : 0
% 3.74/1.61  #Define  : 0
% 3.74/1.61  #Split   : 15
% 3.74/1.61  #Chain   : 0
% 3.74/1.61  #Close   : 0
% 3.74/1.61  
% 3.74/1.61  Ordering : KBO
% 3.74/1.61  
% 3.74/1.61  Simplification rules
% 3.74/1.61  ----------------------
% 3.74/1.61  #Subsume      : 18
% 3.74/1.61  #Demod        : 55
% 3.74/1.61  #Tautology    : 39
% 3.74/1.61  #SimpNegUnit  : 13
% 3.74/1.61  #BackRed      : 7
% 3.74/1.61  
% 3.74/1.61  #Partial instantiations: 0
% 3.74/1.61  #Strategies tried      : 1
% 3.74/1.61  
% 3.74/1.61  Timing (in seconds)
% 3.74/1.61  ----------------------
% 3.74/1.61  Preprocessing        : 0.32
% 3.74/1.61  Parsing              : 0.18
% 3.74/1.61  CNF conversion       : 0.02
% 3.74/1.61  Main loop            : 0.52
% 3.74/1.61  Inferencing          : 0.21
% 3.74/1.61  Reduction            : 0.14
% 3.74/1.61  Demodulation         : 0.09
% 3.74/1.61  BG Simplification    : 0.03
% 3.74/1.61  Subsumption          : 0.10
% 3.74/1.61  Abstraction          : 0.03
% 3.74/1.61  MUC search           : 0.00
% 3.74/1.61  Cooper               : 0.00
% 3.74/1.61  Total                : 0.88
% 3.74/1.61  Index Insertion      : 0.00
% 3.74/1.61  Index Deletion       : 0.00
% 3.74/1.61  Index Matching       : 0.00
% 3.74/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
