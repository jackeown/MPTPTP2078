%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:22 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 380 expanded)
%              Number of leaves         :   31 ( 156 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 (1135 expanded)
%              Number of equality atoms :   38 ( 249 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_112,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_70,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_54,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_57,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_54])).

tff(c_60,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_57])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_63,plain,(
    ! [A_41,B_42,C_43] :
      ( k1_relset_1(A_41,B_42,C_43) = k1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_67,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_63])).

tff(c_79,plain,(
    ! [A_48,B_49] :
      ( k1_relset_1(A_48,A_48,B_49) = A_48
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k2_zfmisc_1(A_48,A_48)))
      | ~ v1_funct_2(B_49,A_48,A_48)
      | ~ v1_funct_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_82,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_79])).

tff(c_85,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_67,c_82])).

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

tff(c_73,plain,(
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

tff(c_77,plain,(
    ! [B_46] :
      ( m1_subset_1('#skF_1'(k1_relat_1(B_46),B_46),k1_relat_1(B_46))
      | k6_partfun1(k1_relat_1(B_46)) = B_46
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_90,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_77])).

tff(c_103,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_36,c_85,c_85,c_90])).

tff(c_115,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_28,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_116,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_28])).

tff(c_132,plain,(
    ! [A_51,B_52,D_53] :
      ( r2_funct_2(A_51,B_52,D_53,D_53)
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_2(D_53,A_51,B_52)
      | ~ v1_funct_1(D_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_134,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_132])).

tff(c_137,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_134])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_137])).

tff(c_141,plain,(
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
    ! [B_57] :
      ( k1_funct_1(B_57,'#skF_1'(k1_relat_1(B_57),B_57)) != '#skF_1'(k1_relat_1(B_57),B_57)
      | k6_partfun1(k1_relat_1(B_57)) = B_57
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8])).

tff(c_169,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_166])).

tff(c_171,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_36,c_85,c_85,c_169])).

tff(c_172,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_171])).

tff(c_140,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_30,plain,(
    ! [C_31] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_31) = C_31
      | ~ m1_subset_1(C_31,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_145,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_140,c_30])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_173,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( k3_funct_2(A_58,B_59,C_60,D_61) = k1_funct_1(C_60,D_61)
      | ~ m1_subset_1(D_61,A_58)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_2(C_60,A_58,B_59)
      | ~ v1_funct_1(C_60)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_175,plain,(
    ! [B_59,C_60] :
      ( k3_funct_2('#skF_2',B_59,C_60,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_60,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_59)))
      | ~ v1_funct_2(C_60,'#skF_2',B_59)
      | ~ v1_funct_1(C_60)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_140,c_173])).

tff(c_185,plain,(
    ! [B_62,C_63] :
      ( k3_funct_2('#skF_2',B_62,C_63,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_63,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_62)))
      | ~ v1_funct_2(C_63,'#skF_2',B_62)
      | ~ v1_funct_1(C_63) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_175])).

tff(c_188,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_185])).

tff(c_191,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_145,c_188])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:48:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.23  
% 1.96/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.24  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.20/1.24  
% 2.20/1.24  %Foreground sorts:
% 2.20/1.24  
% 2.20/1.24  
% 2.20/1.24  %Background operators:
% 2.20/1.24  
% 2.20/1.24  
% 2.20/1.24  %Foreground operators:
% 2.20/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.20/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.20/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.20/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.20/1.24  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.20/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.20/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.20/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.20/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.24  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.20/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.20/1.24  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.20/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.24  
% 2.20/1.25  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.20/1.25  tff(f_112, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t201_funct_2)).
% 2.20/1.25  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.20/1.25  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.20/1.25  tff(f_94, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 2.20/1.25  tff(f_70, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.20/1.25  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.20/1.25  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.20/1.25  tff(f_86, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.20/1.25  tff(f_68, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.20/1.25  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.20/1.25  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.20/1.25  tff(c_54, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.20/1.25  tff(c_57, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_54])).
% 2.20/1.25  tff(c_60, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_57])).
% 2.20/1.25  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.20/1.25  tff(c_34, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.20/1.25  tff(c_63, plain, (![A_41, B_42, C_43]: (k1_relset_1(A_41, B_42, C_43)=k1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.20/1.25  tff(c_67, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_63])).
% 2.20/1.25  tff(c_79, plain, (![A_48, B_49]: (k1_relset_1(A_48, A_48, B_49)=A_48 | ~m1_subset_1(B_49, k1_zfmisc_1(k2_zfmisc_1(A_48, A_48))) | ~v1_funct_2(B_49, A_48, A_48) | ~v1_funct_1(B_49))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.20/1.25  tff(c_82, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_79])).
% 2.20/1.25  tff(c_85, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_67, c_82])).
% 2.20/1.25  tff(c_20, plain, (![A_20]: (k6_relat_1(A_20)=k6_partfun1(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.20/1.25  tff(c_10, plain, (![B_9]: (r2_hidden('#skF_1'(k1_relat_1(B_9), B_9), k1_relat_1(B_9)) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.20/1.25  tff(c_73, plain, (![B_46]: (r2_hidden('#skF_1'(k1_relat_1(B_46), B_46), k1_relat_1(B_46)) | k6_partfun1(k1_relat_1(B_46))=B_46 | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_10])).
% 2.20/1.25  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.25  tff(c_77, plain, (![B_46]: (m1_subset_1('#skF_1'(k1_relat_1(B_46), B_46), k1_relat_1(B_46)) | k6_partfun1(k1_relat_1(B_46))=B_46 | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_73, c_2])).
% 2.20/1.25  tff(c_90, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_85, c_77])).
% 2.20/1.25  tff(c_103, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_36, c_85, c_85, c_90])).
% 2.20/1.25  tff(c_115, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_103])).
% 2.20/1.25  tff(c_28, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.20/1.25  tff(c_116, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_28])).
% 2.20/1.25  tff(c_132, plain, (![A_51, B_52, D_53]: (r2_funct_2(A_51, B_52, D_53, D_53) | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~v1_funct_2(D_53, A_51, B_52) | ~v1_funct_1(D_53))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.20/1.25  tff(c_134, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_132])).
% 2.20/1.25  tff(c_137, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_134])).
% 2.20/1.25  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_137])).
% 2.20/1.25  tff(c_141, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_103])).
% 2.20/1.25  tff(c_8, plain, (![B_9]: (k1_funct_1(B_9, '#skF_1'(k1_relat_1(B_9), B_9))!='#skF_1'(k1_relat_1(B_9), B_9) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.20/1.25  tff(c_166, plain, (![B_57]: (k1_funct_1(B_57, '#skF_1'(k1_relat_1(B_57), B_57))!='#skF_1'(k1_relat_1(B_57), B_57) | k6_partfun1(k1_relat_1(B_57))=B_57 | ~v1_funct_1(B_57) | ~v1_relat_1(B_57))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_8])).
% 2.20/1.25  tff(c_169, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_85, c_166])).
% 2.20/1.25  tff(c_171, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_36, c_85, c_85, c_169])).
% 2.20/1.25  tff(c_172, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_141, c_171])).
% 2.20/1.25  tff(c_140, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_103])).
% 2.20/1.25  tff(c_30, plain, (![C_31]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_31)=C_31 | ~m1_subset_1(C_31, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.20/1.25  tff(c_145, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_140, c_30])).
% 2.20/1.25  tff(c_38, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.20/1.25  tff(c_173, plain, (![A_58, B_59, C_60, D_61]: (k3_funct_2(A_58, B_59, C_60, D_61)=k1_funct_1(C_60, D_61) | ~m1_subset_1(D_61, A_58) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_funct_2(C_60, A_58, B_59) | ~v1_funct_1(C_60) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.20/1.25  tff(c_175, plain, (![B_59, C_60]: (k3_funct_2('#skF_2', B_59, C_60, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_60, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_59))) | ~v1_funct_2(C_60, '#skF_2', B_59) | ~v1_funct_1(C_60) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_140, c_173])).
% 2.20/1.25  tff(c_185, plain, (![B_62, C_63]: (k3_funct_2('#skF_2', B_62, C_63, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_63, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_62))) | ~v1_funct_2(C_63, '#skF_2', B_62) | ~v1_funct_1(C_63))), inference(negUnitSimplification, [status(thm)], [c_38, c_175])).
% 2.20/1.25  tff(c_188, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_185])).
% 2.20/1.25  tff(c_191, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_145, c_188])).
% 2.20/1.25  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_191])).
% 2.20/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.25  
% 2.20/1.25  Inference rules
% 2.20/1.25  ----------------------
% 2.20/1.25  #Ref     : 0
% 2.20/1.25  #Sup     : 31
% 2.20/1.25  #Fact    : 0
% 2.20/1.25  #Define  : 0
% 2.20/1.25  #Split   : 1
% 2.20/1.25  #Chain   : 0
% 2.20/1.25  #Close   : 0
% 2.20/1.25  
% 2.20/1.25  Ordering : KBO
% 2.20/1.25  
% 2.20/1.25  Simplification rules
% 2.20/1.25  ----------------------
% 2.20/1.25  #Subsume      : 0
% 2.20/1.25  #Demod        : 54
% 2.20/1.25  #Tautology    : 17
% 2.20/1.25  #SimpNegUnit  : 7
% 2.20/1.25  #BackRed      : 2
% 2.20/1.25  
% 2.20/1.25  #Partial instantiations: 0
% 2.20/1.25  #Strategies tried      : 1
% 2.20/1.25  
% 2.20/1.25  Timing (in seconds)
% 2.20/1.25  ----------------------
% 2.20/1.26  Preprocessing        : 0.32
% 2.20/1.26  Parsing              : 0.17
% 2.20/1.26  CNF conversion       : 0.02
% 2.20/1.26  Main loop            : 0.17
% 2.20/1.26  Inferencing          : 0.06
% 2.20/1.26  Reduction            : 0.06
% 2.20/1.26  Demodulation         : 0.04
% 2.20/1.26  BG Simplification    : 0.01
% 2.20/1.26  Subsumption          : 0.02
% 2.20/1.26  Abstraction          : 0.01
% 2.20/1.26  MUC search           : 0.00
% 2.20/1.26  Cooper               : 0.00
% 2.20/1.26  Total                : 0.53
% 2.20/1.26  Index Insertion      : 0.00
% 2.20/1.26  Index Deletion       : 0.00
% 2.20/1.26  Index Matching       : 0.00
% 2.20/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
