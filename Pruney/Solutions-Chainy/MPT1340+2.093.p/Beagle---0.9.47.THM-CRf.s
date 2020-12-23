%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:44 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  131 (13228 expanded)
%              Number of leaves         :   41 (4703 expanded)
%              Depth                    :   20
%              Number of atoms          :  287 (39097 expanded)
%              Number of equality atoms :   75 (10595 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_169,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_107,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_123,axiom,(
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

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_147,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_135,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_70,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_78,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_70])).

tff(c_64,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_77,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_70])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_96,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_77,c_58])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_99,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_96,c_4])).

tff(c_102,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_99])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_167,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_relset_1(A_50,B_51,C_52) = k2_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_171,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_167])).

tff(c_56,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_90,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_77,c_56])).

tff(c_172,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_90])).

tff(c_60,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_83,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_60])).

tff(c_84,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_83])).

tff(c_181,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_84])).

tff(c_157,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_161,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_157])).

tff(c_178,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_161])).

tff(c_180,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_96])).

tff(c_224,plain,(
    ! [B_59,A_60,C_61] :
      ( k1_xboole_0 = B_59
      | k1_relset_1(A_60,B_59,C_61) = A_60
      | ~ v1_funct_2(C_61,A_60,B_59)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_227,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_180,c_224])).

tff(c_230,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_178,c_227])).

tff(c_231,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_236,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_181])).

tff(c_235,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_180])).

tff(c_36,plain,(
    ! [A_18,B_19,D_21] :
      ( r2_funct_2(A_18,B_19,D_21,D_21)
      | ~ m1_subset_1(D_21,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(D_21,A_18,B_19)
      | ~ v1_funct_1(D_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_254,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_235,c_36])).

tff(c_269,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_254])).

tff(c_294,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_269])).

tff(c_18,plain,(
    ! [A_8] :
      ( k2_funct_1(k2_funct_1(A_8)) = A_8
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_177,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_171])).

tff(c_234,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_177])).

tff(c_297,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_funct_1(k2_funct_1(C_68))
      | k2_relset_1(A_69,B_70,C_68) != B_70
      | ~ v2_funct_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_funct_2(C_68,A_69,B_70)
      | ~ v1_funct_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_300,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_235,c_297])).

tff(c_303,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_236,c_54,c_234,c_300])).

tff(c_304,plain,(
    ! [C_71,B_72,A_73] :
      ( v1_funct_2(k2_funct_1(C_71),B_72,A_73)
      | k2_relset_1(A_73,B_72,C_71) != B_72
      | ~ v2_funct_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72)))
      | ~ v1_funct_2(C_71,A_73,B_72)
      | ~ v1_funct_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_307,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_235,c_304])).

tff(c_310,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_236,c_54,c_234,c_307])).

tff(c_14,plain,(
    ! [A_7] :
      ( k2_relat_1(k2_funct_1(A_7)) = k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_6] :
      ( v2_funct_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_318,plain,(
    ! [C_77,B_78,A_79] :
      ( m1_subset_1(k2_funct_1(C_77),k1_zfmisc_1(k2_zfmisc_1(B_78,A_79)))
      | k2_relset_1(A_79,B_78,C_77) != B_78
      | ~ v2_funct_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78)))
      | ~ v1_funct_2(C_77,A_79,B_78)
      | ~ v1_funct_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_22,plain,(
    ! [A_12,B_13,C_14] :
      ( k2_relset_1(A_12,B_13,C_14) = k2_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_390,plain,(
    ! [B_83,A_84,C_85] :
      ( k2_relset_1(B_83,A_84,k2_funct_1(C_85)) = k2_relat_1(k2_funct_1(C_85))
      | k2_relset_1(A_84,B_83,C_85) != B_83
      | ~ v2_funct_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83)))
      | ~ v1_funct_2(C_85,A_84,B_83)
      | ~ v1_funct_1(C_85) ) ),
    inference(resolution,[status(thm)],[c_318,c_22])).

tff(c_396,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_235,c_390])).

tff(c_400,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_236,c_54,c_234,c_396])).

tff(c_44,plain,(
    ! [C_24,A_22,B_23] :
      ( v1_funct_1(k2_funct_1(C_24))
      | k2_relset_1(A_22,B_23,C_24) != B_23
      | ~ v2_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_491,plain,(
    ! [C_106,B_107,A_108] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_106)))
      | k2_relset_1(B_107,A_108,k2_funct_1(C_106)) != A_108
      | ~ v2_funct_1(k2_funct_1(C_106))
      | ~ v1_funct_2(k2_funct_1(C_106),B_107,A_108)
      | ~ v1_funct_1(k2_funct_1(C_106))
      | k2_relset_1(A_108,B_107,C_106) != B_107
      | ~ v2_funct_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107)))
      | ~ v1_funct_2(C_106,A_108,B_107)
      | ~ v1_funct_1(C_106) ) ),
    inference(resolution,[status(thm)],[c_318,c_44])).

tff(c_497,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_235,c_491])).

tff(c_501,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_236,c_54,c_234,c_303,c_310,c_400,c_497])).

tff(c_502,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_501])).

tff(c_512,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_502])).

tff(c_516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_62,c_54,c_512])).

tff(c_517,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_519,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_517])).

tff(c_522,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_519])).

tff(c_526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_62,c_54,c_522])).

tff(c_528,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_517])).

tff(c_534,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_400])).

tff(c_518,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_50,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_tops_2(A_27,B_28,C_29) = k2_funct_1(C_29)
      | ~ v2_funct_1(C_29)
      | k2_relset_1(A_27,B_28,C_29) != B_28
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(C_29,A_27,B_28)
      | ~ v1_funct_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_578,plain,(
    ! [B_118,A_119,C_120] :
      ( k2_tops_2(B_118,A_119,k2_funct_1(C_120)) = k2_funct_1(k2_funct_1(C_120))
      | ~ v2_funct_1(k2_funct_1(C_120))
      | k2_relset_1(B_118,A_119,k2_funct_1(C_120)) != A_119
      | ~ v1_funct_2(k2_funct_1(C_120),B_118,A_119)
      | ~ v1_funct_1(k2_funct_1(C_120))
      | k2_relset_1(A_119,B_118,C_120) != B_118
      | ~ v2_funct_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_119,B_118)))
      | ~ v1_funct_2(C_120,A_119,B_118)
      | ~ v1_funct_1(C_120) ) ),
    inference(resolution,[status(thm)],[c_318,c_50])).

tff(c_584,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_235,c_578])).

tff(c_588,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_236,c_54,c_234,c_303,c_310,c_534,c_518,c_584])).

tff(c_311,plain,(
    ! [A_74,B_75,C_76] :
      ( k2_tops_2(A_74,B_75,C_76) = k2_funct_1(C_76)
      | ~ v2_funct_1(C_76)
      | k2_relset_1(A_74,B_75,C_76) != B_75
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_2(C_76,A_74,B_75)
      | ~ v1_funct_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_314,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_235,c_311])).

tff(c_317,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_236,c_234,c_54,c_314])).

tff(c_52,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_105,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_78,c_78,c_77,c_77,c_77,c_52])).

tff(c_179,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_172,c_172,c_105])).

tff(c_232,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_231,c_231,c_179])).

tff(c_374,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_232])).

tff(c_589,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_374])).

tff(c_596,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_589])).

tff(c_599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_62,c_54,c_294,c_596])).

tff(c_600,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_48,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(k2_struct_0(A_26))
      | ~ l1_struct_0(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_186,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_48])).

tff(c_190,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_186])).

tff(c_191,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_190])).

tff(c_608,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_191])).

tff(c_612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_608])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:51:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.52  
% 3.05/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.52  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.40/1.52  
% 3.40/1.52  %Foreground sorts:
% 3.40/1.52  
% 3.40/1.52  
% 3.40/1.52  %Background operators:
% 3.40/1.52  
% 3.40/1.52  
% 3.40/1.52  %Foreground operators:
% 3.40/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.40/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.40/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.40/1.52  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.40/1.52  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.40/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.40/1.52  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.40/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.40/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.40/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.40/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.40/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.40/1.52  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.40/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.40/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.40/1.52  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.40/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.52  
% 3.40/1.55  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.40/1.55  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.40/1.55  tff(f_169, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.40/1.55  tff(f_127, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.40/1.55  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.40/1.55  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.40/1.55  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.40/1.55  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.40/1.55  tff(f_107, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.40/1.55  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.40/1.55  tff(f_123, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.40/1.55  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.40/1.55  tff(f_47, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.40/1.55  tff(f_147, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.40/1.55  tff(f_135, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.40/1.55  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.40/1.55  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.40/1.55  tff(c_68, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.40/1.55  tff(c_70, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.40/1.55  tff(c_78, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_70])).
% 3.40/1.55  tff(c_64, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.40/1.55  tff(c_77, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_70])).
% 3.40/1.55  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.40/1.55  tff(c_96, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_77, c_58])).
% 3.40/1.55  tff(c_4, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.40/1.55  tff(c_99, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_96, c_4])).
% 3.40/1.55  tff(c_102, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_99])).
% 3.40/1.55  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.40/1.55  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.40/1.55  tff(c_167, plain, (![A_50, B_51, C_52]: (k2_relset_1(A_50, B_51, C_52)=k2_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.40/1.55  tff(c_171, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_167])).
% 3.40/1.55  tff(c_56, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.40/1.55  tff(c_90, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_77, c_56])).
% 3.40/1.55  tff(c_172, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_90])).
% 3.40/1.55  tff(c_60, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.40/1.55  tff(c_83, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_60])).
% 3.40/1.55  tff(c_84, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_83])).
% 3.40/1.55  tff(c_181, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_84])).
% 3.40/1.55  tff(c_157, plain, (![A_46, B_47, C_48]: (k1_relset_1(A_46, B_47, C_48)=k1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.40/1.55  tff(c_161, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_157])).
% 3.40/1.55  tff(c_178, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_161])).
% 3.40/1.55  tff(c_180, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_96])).
% 3.40/1.55  tff(c_224, plain, (![B_59, A_60, C_61]: (k1_xboole_0=B_59 | k1_relset_1(A_60, B_59, C_61)=A_60 | ~v1_funct_2(C_61, A_60, B_59) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.40/1.55  tff(c_227, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_180, c_224])).
% 3.40/1.55  tff(c_230, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_178, c_227])).
% 3.40/1.55  tff(c_231, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_230])).
% 3.40/1.55  tff(c_236, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_181])).
% 3.40/1.55  tff(c_235, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_180])).
% 3.40/1.55  tff(c_36, plain, (![A_18, B_19, D_21]: (r2_funct_2(A_18, B_19, D_21, D_21) | ~m1_subset_1(D_21, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_2(D_21, A_18, B_19) | ~v1_funct_1(D_21))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.40/1.55  tff(c_254, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_235, c_36])).
% 3.40/1.55  tff(c_269, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_254])).
% 3.40/1.55  tff(c_294, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_236, c_269])).
% 3.40/1.55  tff(c_18, plain, (![A_8]: (k2_funct_1(k2_funct_1(A_8))=A_8 | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.40/1.55  tff(c_177, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_171])).
% 3.40/1.55  tff(c_234, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_177])).
% 3.40/1.55  tff(c_297, plain, (![C_68, A_69, B_70]: (v1_funct_1(k2_funct_1(C_68)) | k2_relset_1(A_69, B_70, C_68)!=B_70 | ~v2_funct_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_funct_2(C_68, A_69, B_70) | ~v1_funct_1(C_68))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.40/1.55  tff(c_300, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_235, c_297])).
% 3.40/1.55  tff(c_303, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_236, c_54, c_234, c_300])).
% 3.40/1.55  tff(c_304, plain, (![C_71, B_72, A_73]: (v1_funct_2(k2_funct_1(C_71), B_72, A_73) | k2_relset_1(A_73, B_72, C_71)!=B_72 | ~v2_funct_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))) | ~v1_funct_2(C_71, A_73, B_72) | ~v1_funct_1(C_71))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.40/1.55  tff(c_307, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_235, c_304])).
% 3.40/1.55  tff(c_310, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_236, c_54, c_234, c_307])).
% 3.40/1.55  tff(c_14, plain, (![A_7]: (k2_relat_1(k2_funct_1(A_7))=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.40/1.55  tff(c_8, plain, (![A_6]: (v2_funct_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.40/1.55  tff(c_318, plain, (![C_77, B_78, A_79]: (m1_subset_1(k2_funct_1(C_77), k1_zfmisc_1(k2_zfmisc_1(B_78, A_79))) | k2_relset_1(A_79, B_78, C_77)!=B_78 | ~v2_funct_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))) | ~v1_funct_2(C_77, A_79, B_78) | ~v1_funct_1(C_77))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.40/1.55  tff(c_22, plain, (![A_12, B_13, C_14]: (k2_relset_1(A_12, B_13, C_14)=k2_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.40/1.55  tff(c_390, plain, (![B_83, A_84, C_85]: (k2_relset_1(B_83, A_84, k2_funct_1(C_85))=k2_relat_1(k2_funct_1(C_85)) | k2_relset_1(A_84, B_83, C_85)!=B_83 | ~v2_funct_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))) | ~v1_funct_2(C_85, A_84, B_83) | ~v1_funct_1(C_85))), inference(resolution, [status(thm)], [c_318, c_22])).
% 3.40/1.55  tff(c_396, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_235, c_390])).
% 3.40/1.55  tff(c_400, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_236, c_54, c_234, c_396])).
% 3.40/1.55  tff(c_44, plain, (![C_24, A_22, B_23]: (v1_funct_1(k2_funct_1(C_24)) | k2_relset_1(A_22, B_23, C_24)!=B_23 | ~v2_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.40/1.55  tff(c_491, plain, (![C_106, B_107, A_108]: (v1_funct_1(k2_funct_1(k2_funct_1(C_106))) | k2_relset_1(B_107, A_108, k2_funct_1(C_106))!=A_108 | ~v2_funct_1(k2_funct_1(C_106)) | ~v1_funct_2(k2_funct_1(C_106), B_107, A_108) | ~v1_funct_1(k2_funct_1(C_106)) | k2_relset_1(A_108, B_107, C_106)!=B_107 | ~v2_funct_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))) | ~v1_funct_2(C_106, A_108, B_107) | ~v1_funct_1(C_106))), inference(resolution, [status(thm)], [c_318, c_44])).
% 3.40/1.55  tff(c_497, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_235, c_491])).
% 3.40/1.55  tff(c_501, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_236, c_54, c_234, c_303, c_310, c_400, c_497])).
% 3.40/1.55  tff(c_502, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_501])).
% 3.40/1.55  tff(c_512, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_502])).
% 3.40/1.55  tff(c_516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_62, c_54, c_512])).
% 3.40/1.55  tff(c_517, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_501])).
% 3.40/1.55  tff(c_519, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_517])).
% 3.40/1.55  tff(c_522, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_519])).
% 3.40/1.55  tff(c_526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_62, c_54, c_522])).
% 3.40/1.55  tff(c_528, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_517])).
% 3.40/1.55  tff(c_534, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_528, c_400])).
% 3.40/1.55  tff(c_518, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_501])).
% 3.40/1.55  tff(c_50, plain, (![A_27, B_28, C_29]: (k2_tops_2(A_27, B_28, C_29)=k2_funct_1(C_29) | ~v2_funct_1(C_29) | k2_relset_1(A_27, B_28, C_29)!=B_28 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(C_29, A_27, B_28) | ~v1_funct_1(C_29))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.40/1.55  tff(c_578, plain, (![B_118, A_119, C_120]: (k2_tops_2(B_118, A_119, k2_funct_1(C_120))=k2_funct_1(k2_funct_1(C_120)) | ~v2_funct_1(k2_funct_1(C_120)) | k2_relset_1(B_118, A_119, k2_funct_1(C_120))!=A_119 | ~v1_funct_2(k2_funct_1(C_120), B_118, A_119) | ~v1_funct_1(k2_funct_1(C_120)) | k2_relset_1(A_119, B_118, C_120)!=B_118 | ~v2_funct_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_119, B_118))) | ~v1_funct_2(C_120, A_119, B_118) | ~v1_funct_1(C_120))), inference(resolution, [status(thm)], [c_318, c_50])).
% 3.40/1.55  tff(c_584, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_235, c_578])).
% 3.40/1.55  tff(c_588, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_236, c_54, c_234, c_303, c_310, c_534, c_518, c_584])).
% 3.40/1.55  tff(c_311, plain, (![A_74, B_75, C_76]: (k2_tops_2(A_74, B_75, C_76)=k2_funct_1(C_76) | ~v2_funct_1(C_76) | k2_relset_1(A_74, B_75, C_76)!=B_75 | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_2(C_76, A_74, B_75) | ~v1_funct_1(C_76))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.40/1.55  tff(c_314, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_235, c_311])).
% 3.40/1.55  tff(c_317, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_236, c_234, c_54, c_314])).
% 3.40/1.55  tff(c_52, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.40/1.55  tff(c_105, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_78, c_78, c_77, c_77, c_77, c_52])).
% 3.40/1.55  tff(c_179, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_172, c_172, c_105])).
% 3.40/1.55  tff(c_232, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_231, c_231, c_179])).
% 3.40/1.55  tff(c_374, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_317, c_232])).
% 3.40/1.55  tff(c_589, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_588, c_374])).
% 3.40/1.55  tff(c_596, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_589])).
% 3.40/1.55  tff(c_599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_62, c_54, c_294, c_596])).
% 3.40/1.55  tff(c_600, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_230])).
% 3.40/1.55  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.40/1.55  tff(c_48, plain, (![A_26]: (~v1_xboole_0(k2_struct_0(A_26)) | ~l1_struct_0(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.40/1.55  tff(c_186, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_172, c_48])).
% 3.40/1.55  tff(c_190, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_186])).
% 3.40/1.55  tff(c_191, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_190])).
% 3.40/1.55  tff(c_608, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_600, c_191])).
% 3.40/1.55  tff(c_612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_608])).
% 3.40/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.55  
% 3.40/1.55  Inference rules
% 3.40/1.55  ----------------------
% 3.40/1.55  #Ref     : 0
% 3.40/1.55  #Sup     : 123
% 3.40/1.55  #Fact    : 0
% 3.40/1.55  #Define  : 0
% 3.40/1.55  #Split   : 5
% 3.40/1.55  #Chain   : 0
% 3.40/1.55  #Close   : 0
% 3.40/1.55  
% 3.40/1.55  Ordering : KBO
% 3.40/1.55  
% 3.40/1.55  Simplification rules
% 3.40/1.55  ----------------------
% 3.40/1.55  #Subsume      : 4
% 3.40/1.55  #Demod        : 151
% 3.40/1.55  #Tautology    : 74
% 3.40/1.55  #SimpNegUnit  : 1
% 3.40/1.55  #BackRed      : 26
% 3.40/1.55  
% 3.40/1.55  #Partial instantiations: 0
% 3.40/1.55  #Strategies tried      : 1
% 3.40/1.55  
% 3.40/1.55  Timing (in seconds)
% 3.40/1.55  ----------------------
% 3.40/1.55  Preprocessing        : 0.36
% 3.40/1.55  Parsing              : 0.19
% 3.40/1.55  CNF conversion       : 0.02
% 3.40/1.55  Main loop            : 0.36
% 3.40/1.55  Inferencing          : 0.12
% 3.40/1.55  Reduction            : 0.12
% 3.40/1.55  Demodulation         : 0.08
% 3.40/1.55  BG Simplification    : 0.02
% 3.40/1.55  Subsumption          : 0.07
% 3.40/1.55  Abstraction          : 0.02
% 3.40/1.55  MUC search           : 0.00
% 3.40/1.55  Cooper               : 0.00
% 3.40/1.55  Total                : 0.77
% 3.40/1.55  Index Insertion      : 0.00
% 3.40/1.55  Index Deletion       : 0.00
% 3.40/1.55  Index Matching       : 0.00
% 3.40/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
