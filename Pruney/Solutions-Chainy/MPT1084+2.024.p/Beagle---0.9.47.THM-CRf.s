%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:22 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 388 expanded)
%              Number of leaves         :   31 ( 159 expanded)
%              Depth                    :   11
%              Number of atoms          :  147 (1171 expanded)
%              Number of equality atoms :   37 ( 251 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ! [C] :
                  ( m1_subset_1(C,A)
                 => k3_funct_2(A,A,B,C) = C )
             => r2_funct_2(A,A,B,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_70,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_52,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_55,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_52])).

tff(c_58,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_55])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_32,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_61,plain,(
    ! [A_41,B_42,C_43] :
      ( k1_relset_1(A_41,B_42,C_43) = k1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_65,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_61])).

tff(c_77,plain,(
    ! [A_48,B_49] :
      ( k1_relset_1(A_48,A_48,B_49) = A_48
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k2_zfmisc_1(A_48,A_48)))
      | ~ v1_funct_2(B_49,A_48,A_48)
      | ~ v1_funct_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_80,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_77])).

tff(c_83,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_65,c_80])).

tff(c_20,plain,(
    ! [A_20] : k6_relat_1(A_20) = k6_partfun1(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_9),B_9),k1_relat_1(B_9))
      | k6_relat_1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    ! [B_46] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_46),B_46),k1_relat_1(B_46))
      | k6_partfun1(k1_relat_1(B_46)) = B_46
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [B_46] :
      ( m1_subset_1('#skF_1'(k1_relat_1(B_46),B_46),k1_relat_1(B_46))
      | k6_partfun1(k1_relat_1(B_46)) = B_46
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_71,c_2])).

tff(c_91,plain,
    ( m1_subset_1('#skF_1'(k1_relat_1('#skF_3'),'#skF_3'),'#skF_2')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_75])).

tff(c_103,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_34,c_83,c_83,c_91])).

tff(c_113,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_26,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_114,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_26])).

tff(c_146,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( r2_funct_2(A_56,B_57,C_58,C_58)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_2(D_59,A_56,B_57)
      | ~ v1_funct_1(D_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_2(C_58,A_56,B_57)
      | ~ v1_funct_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_148,plain,(
    ! [C_58] :
      ( r2_funct_2('#skF_2','#skF_2',C_58,C_58)
      | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_58,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_58) ) ),
    inference(resolution,[status(thm)],[c_30,c_146])).

tff(c_152,plain,(
    ! [C_60] :
      ( r2_funct_2('#skF_2','#skF_2',C_60,C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_60,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_148])).

tff(c_154,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_152])).

tff(c_157,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_154])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_157])).

tff(c_161,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_8,plain,(
    ! [B_9] :
      ( k1_funct_1(B_9,'#skF_1'(k1_relat_1(B_9),B_9)) != '#skF_1'(k1_relat_1(B_9),B_9)
      | k6_relat_1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_166,plain,(
    ! [B_61] :
      ( k1_funct_1(B_61,'#skF_1'(k1_relat_1(B_61),B_61)) != '#skF_1'(k1_relat_1(B_61),B_61)
      | k6_partfun1(k1_relat_1(B_61)) = B_61
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8])).

tff(c_169,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_166])).

tff(c_171,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_34,c_83,c_83,c_169])).

tff(c_172,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_171])).

tff(c_160,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_28,plain,(
    ! [C_31] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_31) = C_31
      | ~ m1_subset_1(C_31,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_165,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_160,c_28])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_187,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( k3_funct_2(A_62,B_63,C_64,D_65) = k1_funct_1(C_64,D_65)
      | ~ m1_subset_1(D_65,A_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_2(C_64,A_62,B_63)
      | ~ v1_funct_1(C_64)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_189,plain,(
    ! [B_63,C_64] :
      ( k3_funct_2('#skF_2',B_63,C_64,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_64,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_63)))
      | ~ v1_funct_2(C_64,'#skF_2',B_63)
      | ~ v1_funct_1(C_64)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_160,c_187])).

tff(c_199,plain,(
    ! [B_66,C_67] :
      ( k3_funct_2('#skF_2',B_66,C_67,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_67,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_66)))
      | ~ v1_funct_2(C_67,'#skF_2',B_66)
      | ~ v1_funct_1(C_67) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_189])).

tff(c_202,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_199])).

tff(c_205,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_165,c_202])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:00:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.26  
% 2.27/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.26  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.27/1.26  
% 2.27/1.26  %Foreground sorts:
% 2.27/1.26  
% 2.27/1.26  
% 2.27/1.26  %Background operators:
% 2.27/1.26  
% 2.27/1.26  
% 2.27/1.26  %Foreground operators:
% 2.27/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.27/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.27/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.27/1.26  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.27/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.27/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.27/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.26  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.27/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.26  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.27/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.26  
% 2.38/1.28  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.38/1.28  tff(f_110, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 2.38/1.28  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.38/1.28  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.38/1.28  tff(f_92, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 2.38/1.28  tff(f_70, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.38/1.28  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.38/1.28  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.38/1.28  tff(f_84, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 2.38/1.28  tff(f_68, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.38/1.28  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.38/1.28  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.38/1.28  tff(c_52, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.28  tff(c_55, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_52])).
% 2.38/1.28  tff(c_58, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_55])).
% 2.38/1.28  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.38/1.28  tff(c_32, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.38/1.28  tff(c_61, plain, (![A_41, B_42, C_43]: (k1_relset_1(A_41, B_42, C_43)=k1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.38/1.28  tff(c_65, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_61])).
% 2.38/1.28  tff(c_77, plain, (![A_48, B_49]: (k1_relset_1(A_48, A_48, B_49)=A_48 | ~m1_subset_1(B_49, k1_zfmisc_1(k2_zfmisc_1(A_48, A_48))) | ~v1_funct_2(B_49, A_48, A_48) | ~v1_funct_1(B_49))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.38/1.28  tff(c_80, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_77])).
% 2.38/1.28  tff(c_83, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_65, c_80])).
% 2.38/1.28  tff(c_20, plain, (![A_20]: (k6_relat_1(A_20)=k6_partfun1(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.38/1.28  tff(c_10, plain, (![B_9]: (r2_hidden('#skF_1'(k1_relat_1(B_9), B_9), k1_relat_1(B_9)) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.38/1.28  tff(c_71, plain, (![B_46]: (r2_hidden('#skF_1'(k1_relat_1(B_46), B_46), k1_relat_1(B_46)) | k6_partfun1(k1_relat_1(B_46))=B_46 | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_10])).
% 2.38/1.28  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.38/1.28  tff(c_75, plain, (![B_46]: (m1_subset_1('#skF_1'(k1_relat_1(B_46), B_46), k1_relat_1(B_46)) | k6_partfun1(k1_relat_1(B_46))=B_46 | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_71, c_2])).
% 2.38/1.28  tff(c_91, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_3'), '#skF_3'), '#skF_2') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_83, c_75])).
% 2.38/1.28  tff(c_103, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_34, c_83, c_83, c_91])).
% 2.38/1.28  tff(c_113, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_103])).
% 2.38/1.28  tff(c_26, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.38/1.28  tff(c_114, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_26])).
% 2.38/1.28  tff(c_146, plain, (![A_56, B_57, C_58, D_59]: (r2_funct_2(A_56, B_57, C_58, C_58) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_2(D_59, A_56, B_57) | ~v1_funct_1(D_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_2(C_58, A_56, B_57) | ~v1_funct_1(C_58))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.38/1.28  tff(c_148, plain, (![C_58]: (r2_funct_2('#skF_2', '#skF_2', C_58, C_58) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(C_58, '#skF_2', '#skF_2') | ~v1_funct_1(C_58))), inference(resolution, [status(thm)], [c_30, c_146])).
% 2.38/1.28  tff(c_152, plain, (![C_60]: (r2_funct_2('#skF_2', '#skF_2', C_60, C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(C_60, '#skF_2', '#skF_2') | ~v1_funct_1(C_60))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_148])).
% 2.38/1.28  tff(c_154, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_152])).
% 2.38/1.28  tff(c_157, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_154])).
% 2.38/1.28  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_157])).
% 2.38/1.28  tff(c_161, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_103])).
% 2.38/1.28  tff(c_8, plain, (![B_9]: (k1_funct_1(B_9, '#skF_1'(k1_relat_1(B_9), B_9))!='#skF_1'(k1_relat_1(B_9), B_9) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.38/1.28  tff(c_166, plain, (![B_61]: (k1_funct_1(B_61, '#skF_1'(k1_relat_1(B_61), B_61))!='#skF_1'(k1_relat_1(B_61), B_61) | k6_partfun1(k1_relat_1(B_61))=B_61 | ~v1_funct_1(B_61) | ~v1_relat_1(B_61))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_8])).
% 2.38/1.28  tff(c_169, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_83, c_166])).
% 2.38/1.28  tff(c_171, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_34, c_83, c_83, c_169])).
% 2.38/1.28  tff(c_172, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_161, c_171])).
% 2.38/1.28  tff(c_160, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_103])).
% 2.38/1.28  tff(c_28, plain, (![C_31]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_31)=C_31 | ~m1_subset_1(C_31, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.38/1.28  tff(c_165, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_160, c_28])).
% 2.38/1.28  tff(c_36, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.38/1.28  tff(c_187, plain, (![A_62, B_63, C_64, D_65]: (k3_funct_2(A_62, B_63, C_64, D_65)=k1_funct_1(C_64, D_65) | ~m1_subset_1(D_65, A_62) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_funct_2(C_64, A_62, B_63) | ~v1_funct_1(C_64) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.38/1.28  tff(c_189, plain, (![B_63, C_64]: (k3_funct_2('#skF_2', B_63, C_64, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_64, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_63))) | ~v1_funct_2(C_64, '#skF_2', B_63) | ~v1_funct_1(C_64) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_160, c_187])).
% 2.38/1.28  tff(c_199, plain, (![B_66, C_67]: (k3_funct_2('#skF_2', B_66, C_67, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_67, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_66))) | ~v1_funct_2(C_67, '#skF_2', B_66) | ~v1_funct_1(C_67))), inference(negUnitSimplification, [status(thm)], [c_36, c_189])).
% 2.38/1.28  tff(c_202, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_199])).
% 2.38/1.28  tff(c_205, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_165, c_202])).
% 2.38/1.28  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_205])).
% 2.38/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.28  
% 2.38/1.28  Inference rules
% 2.38/1.28  ----------------------
% 2.38/1.28  #Ref     : 0
% 2.38/1.28  #Sup     : 34
% 2.38/1.28  #Fact    : 0
% 2.38/1.28  #Define  : 0
% 2.38/1.28  #Split   : 2
% 2.38/1.28  #Chain   : 0
% 2.38/1.28  #Close   : 0
% 2.38/1.28  
% 2.38/1.28  Ordering : KBO
% 2.38/1.28  
% 2.38/1.28  Simplification rules
% 2.38/1.28  ----------------------
% 2.38/1.28  #Subsume      : 0
% 2.38/1.28  #Demod        : 61
% 2.38/1.28  #Tautology    : 20
% 2.38/1.28  #SimpNegUnit  : 7
% 2.38/1.28  #BackRed      : 2
% 2.38/1.28  
% 2.38/1.28  #Partial instantiations: 0
% 2.38/1.28  #Strategies tried      : 1
% 2.38/1.28  
% 2.38/1.28  Timing (in seconds)
% 2.38/1.28  ----------------------
% 2.38/1.28  Preprocessing        : 0.33
% 2.38/1.28  Parsing              : 0.17
% 2.38/1.28  CNF conversion       : 0.02
% 2.38/1.28  Main loop            : 0.19
% 2.38/1.28  Inferencing          : 0.06
% 2.38/1.28  Reduction            : 0.07
% 2.38/1.28  Demodulation         : 0.05
% 2.38/1.28  BG Simplification    : 0.02
% 2.38/1.28  Subsumption          : 0.03
% 2.38/1.28  Abstraction          : 0.01
% 2.38/1.28  MUC search           : 0.00
% 2.38/1.28  Cooper               : 0.00
% 2.38/1.28  Total                : 0.55
% 2.38/1.28  Index Insertion      : 0.00
% 2.38/1.28  Index Deletion       : 0.00
% 2.38/1.28  Index Matching       : 0.00
% 2.38/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
