%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:38 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 102 expanded)
%              Number of leaves         :   23 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :  109 ( 298 expanded)
%              Number of equality atoms :   10 (  33 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
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

tff(c_22,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [F_28] :
      ( k1_funct_1('#skF_6',F_28) != '#skF_7'
      | ~ r2_hidden(F_28,'#skF_5')
      | ~ m1_subset_1(F_28,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_54,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_5')) != '#skF_7'
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_49])).

tff(c_90,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_94,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_90])).

tff(c_95,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_28,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_123,plain,(
    ! [E_44,C_42,D_40,A_43,B_41] :
      ( r2_hidden('#skF_2'(D_40,B_41,C_42,A_43,E_44),A_43)
      | ~ r2_hidden(E_44,k7_relset_1(A_43,B_41,D_40,C_42))
      | ~ m1_subset_1(D_40,k1_zfmisc_1(k2_zfmisc_1(A_43,B_41)))
      | ~ v1_funct_2(D_40,A_43,B_41)
      | ~ v1_funct_1(D_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_131,plain,(
    ! [C_42,E_44] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_4',C_42,'#skF_3',E_44),'#skF_3')
      | ~ r2_hidden(E_44,k7_relset_1('#skF_3','#skF_4','#skF_6',C_42))
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_123])).

tff(c_217,plain,(
    ! [C_54,E_55] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_4',C_54,'#skF_3',E_55),'#skF_3')
      | ~ r2_hidden(E_55,k7_relset_1('#skF_3','#skF_4','#skF_6',C_54)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_131])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_220,plain,(
    ! [C_54,E_55] :
      ( m1_subset_1('#skF_2'('#skF_6','#skF_4',C_54,'#skF_3',E_55),'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ r2_hidden(E_55,k7_relset_1('#skF_3','#skF_4','#skF_6',C_54)) ) ),
    inference(resolution,[status(thm)],[c_217,c_6])).

tff(c_228,plain,(
    ! [C_56,E_57] :
      ( m1_subset_1('#skF_2'('#skF_6','#skF_4',C_56,'#skF_3',E_57),'#skF_3')
      | ~ r2_hidden(E_57,k7_relset_1('#skF_3','#skF_4','#skF_6',C_56)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_220])).

tff(c_246,plain,(
    m1_subset_1('#skF_2'('#skF_6','#skF_4','#skF_5','#skF_3','#skF_7'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_228])).

tff(c_252,plain,(
    ! [B_59,A_61,E_62,C_60,D_58] :
      ( k1_funct_1(D_58,'#skF_2'(D_58,B_59,C_60,A_61,E_62)) = E_62
      | ~ r2_hidden(E_62,k7_relset_1(A_61,B_59,D_58,C_60))
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_61,B_59)))
      | ~ v1_funct_2(D_58,A_61,B_59)
      | ~ v1_funct_1(D_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_260,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_6','#skF_4','#skF_5','#skF_3','#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_252])).

tff(c_268,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_6','#skF_4','#skF_5','#skF_3','#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_260])).

tff(c_109,plain,(
    ! [B_36,C_37,A_38,E_39,D_35] :
      ( r2_hidden('#skF_2'(D_35,B_36,C_37,A_38,E_39),C_37)
      | ~ r2_hidden(E_39,k7_relset_1(A_38,B_36,D_35,C_37))
      | ~ m1_subset_1(D_35,k1_zfmisc_1(k2_zfmisc_1(A_38,B_36)))
      | ~ v1_funct_2(D_35,A_38,B_36)
      | ~ v1_funct_1(D_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_117,plain,(
    ! [C_37,E_39] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_4',C_37,'#skF_3',E_39),C_37)
      | ~ r2_hidden(E_39,k7_relset_1('#skF_3','#skF_4','#skF_6',C_37))
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_109])).

tff(c_137,plain,(
    ! [C_45,E_46] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_4',C_45,'#skF_3',E_46),C_45)
      | ~ r2_hidden(E_46,k7_relset_1('#skF_3','#skF_4','#skF_6',C_45)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_117])).

tff(c_20,plain,(
    ! [F_20] :
      ( k1_funct_1('#skF_6',F_20) != '#skF_7'
      | ~ r2_hidden(F_20,'#skF_5')
      | ~ m1_subset_1(F_20,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_176,plain,(
    ! [E_50] :
      ( k1_funct_1('#skF_6','#skF_2'('#skF_6','#skF_4','#skF_5','#skF_3',E_50)) != '#skF_7'
      | ~ m1_subset_1('#skF_2'('#skF_6','#skF_4','#skF_5','#skF_3',E_50),'#skF_3')
      | ~ r2_hidden(E_50,k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_137,c_20])).

tff(c_196,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_6','#skF_4','#skF_5','#skF_3','#skF_7')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_6','#skF_4','#skF_5','#skF_3','#skF_7'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_176])).

tff(c_293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_268,c_196])).

tff(c_295,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_309,plain,(
    ! [D_66,B_67,C_68,E_70,A_69] :
      ( r2_hidden('#skF_2'(D_66,B_67,C_68,A_69,E_70),A_69)
      | ~ r2_hidden(E_70,k7_relset_1(A_69,B_67,D_66,C_68))
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_69,B_67)))
      | ~ v1_funct_2(D_66,A_69,B_67)
      | ~ v1_funct_1(D_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_317,plain,(
    ! [C_68,E_70] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_4',C_68,'#skF_3',E_70),'#skF_3')
      | ~ r2_hidden(E_70,k7_relset_1('#skF_3','#skF_4','#skF_6',C_68))
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_309])).

tff(c_323,plain,(
    ! [C_71,E_72] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_4',C_71,'#skF_3',E_72),'#skF_3')
      | ~ r2_hidden(E_72,k7_relset_1('#skF_3','#skF_4','#skF_6',C_71)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_317])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_329,plain,(
    ! [E_72,C_71] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(E_72,k7_relset_1('#skF_3','#skF_4','#skF_6',C_71)) ) ),
    inference(resolution,[status(thm)],[c_323,c_2])).

tff(c_334,plain,(
    ! [E_72,C_71] : ~ r2_hidden(E_72,k7_relset_1('#skF_3','#skF_4','#skF_6',C_71)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_329])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:59:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.36  
% 2.32/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.36  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.32/1.36  
% 2.32/1.36  %Foreground sorts:
% 2.32/1.36  
% 2.32/1.36  
% 2.32/1.36  %Background operators:
% 2.32/1.36  
% 2.32/1.36  
% 2.32/1.36  %Foreground operators:
% 2.32/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.32/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.32/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.32/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.32/1.36  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.32/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.32/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.32/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.32/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.32/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.36  
% 2.32/1.38  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 2.32/1.38  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.32/1.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.32/1.38  tff(f_62, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 2.32/1.38  tff(c_22, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.32/1.38  tff(c_10, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~v1_xboole_0(B_6) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.32/1.38  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.38  tff(c_49, plain, (![F_28]: (k1_funct_1('#skF_6', F_28)!='#skF_7' | ~r2_hidden(F_28, '#skF_5') | ~m1_subset_1(F_28, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.32/1.38  tff(c_54, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5'))!='#skF_7' | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_49])).
% 2.32/1.38  tff(c_90, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 2.32/1.38  tff(c_94, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_10, c_90])).
% 2.32/1.38  tff(c_95, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_94])).
% 2.32/1.38  tff(c_28, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.32/1.38  tff(c_26, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.32/1.38  tff(c_24, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.32/1.38  tff(c_123, plain, (![E_44, C_42, D_40, A_43, B_41]: (r2_hidden('#skF_2'(D_40, B_41, C_42, A_43, E_44), A_43) | ~r2_hidden(E_44, k7_relset_1(A_43, B_41, D_40, C_42)) | ~m1_subset_1(D_40, k1_zfmisc_1(k2_zfmisc_1(A_43, B_41))) | ~v1_funct_2(D_40, A_43, B_41) | ~v1_funct_1(D_40))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.32/1.38  tff(c_131, plain, (![C_42, E_44]: (r2_hidden('#skF_2'('#skF_6', '#skF_4', C_42, '#skF_3', E_44), '#skF_3') | ~r2_hidden(E_44, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_42)) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_24, c_123])).
% 2.32/1.38  tff(c_217, plain, (![C_54, E_55]: (r2_hidden('#skF_2'('#skF_6', '#skF_4', C_54, '#skF_3', E_55), '#skF_3') | ~r2_hidden(E_55, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_54)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_131])).
% 2.32/1.38  tff(c_6, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.32/1.38  tff(c_220, plain, (![C_54, E_55]: (m1_subset_1('#skF_2'('#skF_6', '#skF_4', C_54, '#skF_3', E_55), '#skF_3') | v1_xboole_0('#skF_3') | ~r2_hidden(E_55, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_54)))), inference(resolution, [status(thm)], [c_217, c_6])).
% 2.32/1.38  tff(c_228, plain, (![C_56, E_57]: (m1_subset_1('#skF_2'('#skF_6', '#skF_4', C_56, '#skF_3', E_57), '#skF_3') | ~r2_hidden(E_57, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_56)))), inference(negUnitSimplification, [status(thm)], [c_95, c_220])).
% 2.32/1.38  tff(c_246, plain, (m1_subset_1('#skF_2'('#skF_6', '#skF_4', '#skF_5', '#skF_3', '#skF_7'), '#skF_3')), inference(resolution, [status(thm)], [c_22, c_228])).
% 2.32/1.38  tff(c_252, plain, (![B_59, A_61, E_62, C_60, D_58]: (k1_funct_1(D_58, '#skF_2'(D_58, B_59, C_60, A_61, E_62))=E_62 | ~r2_hidden(E_62, k7_relset_1(A_61, B_59, D_58, C_60)) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_61, B_59))) | ~v1_funct_2(D_58, A_61, B_59) | ~v1_funct_1(D_58))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.32/1.38  tff(c_260, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_6', '#skF_4', '#skF_5', '#skF_3', '#skF_7'))='#skF_7' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_252])).
% 2.32/1.38  tff(c_268, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_6', '#skF_4', '#skF_5', '#skF_3', '#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_260])).
% 2.32/1.38  tff(c_109, plain, (![B_36, C_37, A_38, E_39, D_35]: (r2_hidden('#skF_2'(D_35, B_36, C_37, A_38, E_39), C_37) | ~r2_hidden(E_39, k7_relset_1(A_38, B_36, D_35, C_37)) | ~m1_subset_1(D_35, k1_zfmisc_1(k2_zfmisc_1(A_38, B_36))) | ~v1_funct_2(D_35, A_38, B_36) | ~v1_funct_1(D_35))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.32/1.38  tff(c_117, plain, (![C_37, E_39]: (r2_hidden('#skF_2'('#skF_6', '#skF_4', C_37, '#skF_3', E_39), C_37) | ~r2_hidden(E_39, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_37)) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_24, c_109])).
% 2.32/1.38  tff(c_137, plain, (![C_45, E_46]: (r2_hidden('#skF_2'('#skF_6', '#skF_4', C_45, '#skF_3', E_46), C_45) | ~r2_hidden(E_46, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_45)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_117])).
% 2.32/1.38  tff(c_20, plain, (![F_20]: (k1_funct_1('#skF_6', F_20)!='#skF_7' | ~r2_hidden(F_20, '#skF_5') | ~m1_subset_1(F_20, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.32/1.38  tff(c_176, plain, (![E_50]: (k1_funct_1('#skF_6', '#skF_2'('#skF_6', '#skF_4', '#skF_5', '#skF_3', E_50))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_6', '#skF_4', '#skF_5', '#skF_3', E_50), '#skF_3') | ~r2_hidden(E_50, k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5')))), inference(resolution, [status(thm)], [c_137, c_20])).
% 2.32/1.38  tff(c_196, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_6', '#skF_4', '#skF_5', '#skF_3', '#skF_7'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_6', '#skF_4', '#skF_5', '#skF_3', '#skF_7'), '#skF_3')), inference(resolution, [status(thm)], [c_22, c_176])).
% 2.32/1.38  tff(c_293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_246, c_268, c_196])).
% 2.32/1.38  tff(c_295, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_94])).
% 2.32/1.38  tff(c_309, plain, (![D_66, B_67, C_68, E_70, A_69]: (r2_hidden('#skF_2'(D_66, B_67, C_68, A_69, E_70), A_69) | ~r2_hidden(E_70, k7_relset_1(A_69, B_67, D_66, C_68)) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_69, B_67))) | ~v1_funct_2(D_66, A_69, B_67) | ~v1_funct_1(D_66))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.32/1.38  tff(c_317, plain, (![C_68, E_70]: (r2_hidden('#skF_2'('#skF_6', '#skF_4', C_68, '#skF_3', E_70), '#skF_3') | ~r2_hidden(E_70, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_68)) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_24, c_309])).
% 2.32/1.38  tff(c_323, plain, (![C_71, E_72]: (r2_hidden('#skF_2'('#skF_6', '#skF_4', C_71, '#skF_3', E_72), '#skF_3') | ~r2_hidden(E_72, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_71)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_317])).
% 2.32/1.38  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.38  tff(c_329, plain, (![E_72, C_71]: (~v1_xboole_0('#skF_3') | ~r2_hidden(E_72, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_71)))), inference(resolution, [status(thm)], [c_323, c_2])).
% 2.32/1.38  tff(c_334, plain, (![E_72, C_71]: (~r2_hidden(E_72, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_71)))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_329])).
% 2.32/1.38  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_22])).
% 2.32/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.38  
% 2.32/1.38  Inference rules
% 2.32/1.38  ----------------------
% 2.32/1.38  #Ref     : 0
% 2.32/1.38  #Sup     : 60
% 2.32/1.38  #Fact    : 0
% 2.32/1.38  #Define  : 0
% 2.32/1.38  #Split   : 7
% 2.32/1.38  #Chain   : 0
% 2.32/1.38  #Close   : 0
% 2.32/1.38  
% 2.32/1.38  Ordering : KBO
% 2.32/1.38  
% 2.32/1.38  Simplification rules
% 2.32/1.38  ----------------------
% 2.32/1.38  #Subsume      : 9
% 2.32/1.38  #Demod        : 13
% 2.32/1.38  #Tautology    : 8
% 2.32/1.38  #SimpNegUnit  : 6
% 2.32/1.38  #BackRed      : 1
% 2.32/1.38  
% 2.32/1.38  #Partial instantiations: 0
% 2.32/1.38  #Strategies tried      : 1
% 2.32/1.38  
% 2.32/1.38  Timing (in seconds)
% 2.32/1.38  ----------------------
% 2.32/1.38  Preprocessing        : 0.29
% 2.32/1.38  Parsing              : 0.16
% 2.32/1.38  CNF conversion       : 0.02
% 2.32/1.38  Main loop            : 0.24
% 2.32/1.38  Inferencing          : 0.10
% 2.32/1.38  Reduction            : 0.06
% 2.32/1.38  Demodulation         : 0.04
% 2.32/1.38  BG Simplification    : 0.01
% 2.32/1.38  Subsumption          : 0.05
% 2.32/1.38  Abstraction          : 0.01
% 2.32/1.38  MUC search           : 0.00
% 2.32/1.38  Cooper               : 0.00
% 2.32/1.38  Total                : 0.56
% 2.32/1.38  Index Insertion      : 0.00
% 2.32/1.38  Index Deletion       : 0.00
% 2.32/1.38  Index Matching       : 0.00
% 2.32/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
