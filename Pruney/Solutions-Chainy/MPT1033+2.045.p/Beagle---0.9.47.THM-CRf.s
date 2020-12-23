%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:56 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 222 expanded)
%              Number of leaves         :   20 (  82 expanded)
%              Depth                    :    7
%              Number of atoms          :  152 ( 908 expanded)
%              Number of equality atoms :   25 ( 226 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30,plain,(
    ! [A_14,B_15,D_16] :
      ( r2_relset_1(A_14,B_15,D_16,D_16)
      | ~ m1_subset_1(D_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_30])).

tff(c_14,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_29,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_28,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_38,plain,(
    ! [B_19,C_20,A_21] :
      ( k1_xboole_0 = B_19
      | v1_partfun1(C_20,A_21)
      | ~ v1_funct_2(C_20,A_21,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_19)))
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_38])).

tff(c_51,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_44])).

tff(c_52,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_51])).

tff(c_22,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_20,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_41,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_38])).

tff(c_47,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_41])).

tff(c_48,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_47])).

tff(c_16,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_66,plain,(
    ! [D_26,C_27,A_28,B_29] :
      ( D_26 = C_27
      | ~ r1_partfun1(C_27,D_26)
      | ~ v1_partfun1(D_26,A_28)
      | ~ v1_partfun1(C_27,A_28)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1(D_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_68,plain,(
    ! [A_28,B_29] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_28)
      | ~ v1_partfun1('#skF_3',A_28)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_66])).

tff(c_71,plain,(
    ! [A_28,B_29] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_28)
      | ~ v1_partfun1('#skF_3',A_28)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_68])).

tff(c_73,plain,(
    ! [A_30,B_31] :
      ( ~ v1_partfun1('#skF_4',A_30)
      | ~ v1_partfun1('#skF_3',A_30)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_76,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_24,c_73])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_52,c_48,c_76])).

tff(c_81,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_12,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_85,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_12])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_85])).

tff(c_95,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_96,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_101,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_96])).

tff(c_110,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_18])).

tff(c_111,plain,(
    ! [A_32,B_33,D_34] :
      ( r2_relset_1(A_32,B_33,D_34,D_34)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_116,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_110,c_111])).

tff(c_102,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_26])).

tff(c_109,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_24])).

tff(c_6,plain,(
    ! [C_7,B_6] :
      ( v1_partfun1(C_7,k1_xboole_0)
      | ~ v1_funct_2(C_7,k1_xboole_0,B_6)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_6)))
      | ~ v1_funct_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_119,plain,(
    ! [C_35,B_36] :
      ( v1_partfun1(C_35,'#skF_1')
      | ~ v1_funct_2(C_35,'#skF_1',B_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_36)))
      | ~ v1_funct_1(C_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_95,c_95,c_6])).

tff(c_125,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_109,c_119])).

tff(c_131,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_102,c_125])).

tff(c_107,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_20])).

tff(c_122,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_110,c_119])).

tff(c_128,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_107,c_122])).

tff(c_161,plain,(
    ! [D_44,C_45,A_46,B_47] :
      ( D_44 = C_45
      | ~ r1_partfun1(C_45,D_44)
      | ~ v1_partfun1(D_44,A_46)
      | ~ v1_partfun1(C_45,A_46)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_1(D_44)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_163,plain,(
    ! [A_46,B_47] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_46)
      | ~ v1_partfun1('#skF_3',A_46)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_161])).

tff(c_166,plain,(
    ! [A_46,B_47] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_46)
      | ~ v1_partfun1('#skF_3',A_46)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_163])).

tff(c_168,plain,(
    ! [A_48,B_49] :
      ( ~ v1_partfun1('#skF_4',A_48)
      | ~ v1_partfun1('#skF_3',A_48)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_171,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_109,c_168])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_131,c_128,c_171])).

tff(c_176,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_108,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_12])).

tff(c_180,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_108])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:36:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.93/1.19  
% 1.93/1.19  %Foreground sorts:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Background operators:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Foreground operators:
% 1.93/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.93/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.93/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.19  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.93/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.19  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 1.93/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.19  
% 1.93/1.21  tff(f_90, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 1.93/1.21  tff(f_33, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.93/1.21  tff(f_50, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 1.93/1.21  tff(f_67, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 1.93/1.21  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.93/1.21  tff(c_30, plain, (![A_14, B_15, D_16]: (r2_relset_1(A_14, B_15, D_16, D_16) | ~m1_subset_1(D_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.21  tff(c_35, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_30])).
% 1.93/1.21  tff(c_14, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.93/1.21  tff(c_29, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_14])).
% 1.93/1.21  tff(c_28, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.93/1.21  tff(c_26, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.93/1.21  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.93/1.21  tff(c_38, plain, (![B_19, C_20, A_21]: (k1_xboole_0=B_19 | v1_partfun1(C_20, A_21) | ~v1_funct_2(C_20, A_21, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_19))) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.21  tff(c_44, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_38])).
% 1.93/1.21  tff(c_51, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_44])).
% 1.93/1.21  tff(c_52, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_29, c_51])).
% 1.93/1.21  tff(c_22, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.93/1.21  tff(c_20, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.93/1.21  tff(c_41, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_38])).
% 1.93/1.21  tff(c_47, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_41])).
% 1.93/1.21  tff(c_48, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_29, c_47])).
% 1.93/1.21  tff(c_16, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.93/1.21  tff(c_66, plain, (![D_26, C_27, A_28, B_29]: (D_26=C_27 | ~r1_partfun1(C_27, D_26) | ~v1_partfun1(D_26, A_28) | ~v1_partfun1(C_27, A_28) | ~m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1(D_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1(C_27))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.93/1.21  tff(c_68, plain, (![A_28, B_29]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_28) | ~v1_partfun1('#skF_3', A_28) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_66])).
% 1.93/1.21  tff(c_71, plain, (![A_28, B_29]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_28) | ~v1_partfun1('#skF_3', A_28) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_68])).
% 1.93/1.21  tff(c_73, plain, (![A_30, B_31]: (~v1_partfun1('#skF_4', A_30) | ~v1_partfun1('#skF_3', A_30) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(splitLeft, [status(thm)], [c_71])).
% 1.93/1.21  tff(c_76, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_24, c_73])).
% 1.93/1.21  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_52, c_48, c_76])).
% 1.93/1.21  tff(c_81, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_71])).
% 1.93/1.21  tff(c_12, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.93/1.21  tff(c_85, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_12])).
% 1.93/1.21  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_85])).
% 1.93/1.21  tff(c_95, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_14])).
% 1.93/1.21  tff(c_96, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_14])).
% 1.93/1.21  tff(c_101, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_96])).
% 1.93/1.21  tff(c_110, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_18])).
% 1.93/1.21  tff(c_111, plain, (![A_32, B_33, D_34]: (r2_relset_1(A_32, B_33, D_34, D_34) | ~m1_subset_1(D_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.21  tff(c_116, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_110, c_111])).
% 1.93/1.21  tff(c_102, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_26])).
% 1.93/1.21  tff(c_109, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_24])).
% 1.93/1.21  tff(c_6, plain, (![C_7, B_6]: (v1_partfun1(C_7, k1_xboole_0) | ~v1_funct_2(C_7, k1_xboole_0, B_6) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_6))) | ~v1_funct_1(C_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.21  tff(c_119, plain, (![C_35, B_36]: (v1_partfun1(C_35, '#skF_1') | ~v1_funct_2(C_35, '#skF_1', B_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_36))) | ~v1_funct_1(C_35))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_95, c_95, c_6])).
% 1.93/1.21  tff(c_125, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_109, c_119])).
% 1.93/1.21  tff(c_131, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_102, c_125])).
% 1.93/1.21  tff(c_107, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_20])).
% 1.93/1.21  tff(c_122, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_110, c_119])).
% 1.93/1.21  tff(c_128, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_107, c_122])).
% 1.93/1.21  tff(c_161, plain, (![D_44, C_45, A_46, B_47]: (D_44=C_45 | ~r1_partfun1(C_45, D_44) | ~v1_partfun1(D_44, A_46) | ~v1_partfun1(C_45, A_46) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_1(D_44) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_1(C_45))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.93/1.21  tff(c_163, plain, (![A_46, B_47]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_46) | ~v1_partfun1('#skF_3', A_46) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_161])).
% 1.93/1.21  tff(c_166, plain, (![A_46, B_47]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_46) | ~v1_partfun1('#skF_3', A_46) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_163])).
% 1.93/1.21  tff(c_168, plain, (![A_48, B_49]: (~v1_partfun1('#skF_4', A_48) | ~v1_partfun1('#skF_3', A_48) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(splitLeft, [status(thm)], [c_166])).
% 1.93/1.21  tff(c_171, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_109, c_168])).
% 1.93/1.21  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_131, c_128, c_171])).
% 1.93/1.21  tff(c_176, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_166])).
% 1.93/1.21  tff(c_108, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_12])).
% 1.93/1.21  tff(c_180, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_108])).
% 1.93/1.21  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_180])).
% 1.93/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  Inference rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Ref     : 0
% 1.93/1.21  #Sup     : 22
% 1.93/1.21  #Fact    : 0
% 1.93/1.21  #Define  : 0
% 1.93/1.21  #Split   : 3
% 1.93/1.21  #Chain   : 0
% 1.93/1.21  #Close   : 0
% 1.93/1.21  
% 1.93/1.21  Ordering : KBO
% 1.93/1.21  
% 1.93/1.21  Simplification rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Subsume      : 0
% 1.93/1.21  #Demod        : 62
% 1.93/1.21  #Tautology    : 16
% 1.93/1.21  #SimpNegUnit  : 2
% 1.93/1.21  #BackRed      : 15
% 1.93/1.21  
% 1.93/1.21  #Partial instantiations: 0
% 1.93/1.21  #Strategies tried      : 1
% 1.93/1.21  
% 1.93/1.21  Timing (in seconds)
% 1.93/1.21  ----------------------
% 2.10/1.21  Preprocessing        : 0.29
% 2.10/1.21  Parsing              : 0.16
% 2.10/1.21  CNF conversion       : 0.02
% 2.10/1.21  Main loop            : 0.16
% 2.10/1.21  Inferencing          : 0.06
% 2.10/1.21  Reduction            : 0.05
% 2.10/1.21  Demodulation         : 0.04
% 2.10/1.21  BG Simplification    : 0.01
% 2.10/1.21  Subsumption          : 0.02
% 2.10/1.21  Abstraction          : 0.01
% 2.10/1.21  MUC search           : 0.00
% 2.10/1.21  Cooper               : 0.00
% 2.10/1.21  Total                : 0.48
% 2.10/1.21  Index Insertion      : 0.00
% 2.10/1.21  Index Deletion       : 0.00
% 2.10/1.21  Index Matching       : 0.00
% 2.10/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
