%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:07 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 210 expanded)
%              Number of leaves         :   36 (  89 expanded)
%              Depth                    :   16
%              Number of atoms          :  203 ( 859 expanded)
%              Number of equality atoms :    2 (   8 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(u1_waybel_0(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
            <=> ? [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                  & ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ( r1_orders_2(B,D,E)
                       => r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => k2_waybel_0(A,B,C) = k3_funct_2(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_waybel_0)).

tff(f_63,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( m1_subset_1(C,A)
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,A,B)
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                 => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_46,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_42,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_63,plain,(
    ! [B_99,A_100] :
      ( l1_orders_2(B_99)
      | ~ l1_waybel_0(B_99,A_100)
      | ~ l1_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_66,plain,
    ( l1_orders_2('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_63])).

tff(c_69,plain,(
    l1_orders_2('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_66])).

tff(c_18,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_36,plain,(
    ! [A_87,B_88] :
      ( v1_funct_2(u1_waybel_0(A_87,B_88),u1_struct_0(B_88),u1_struct_0(A_87))
      | ~ l1_waybel_0(B_88,A_87)
      | ~ l1_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_38,plain,(
    ! [A_87,B_88] :
      ( v1_funct_1(u1_waybel_0(A_87,B_88))
      | ~ l1_waybel_0(B_88,A_87)
      | ~ l1_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [B_103,A_104] :
      ( m1_subset_1(B_103,A_104)
      | ~ r2_hidden(B_103,A_104)
      | v1_xboole_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_83,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_75])).

tff(c_34,plain,(
    ! [A_87,B_88] :
      ( m1_subset_1(u1_waybel_0(A_87,B_88),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_88),u1_struct_0(A_87))))
      | ~ l1_waybel_0(B_88,A_87)
      | ~ l1_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_28,plain,(
    ! [A_24,B_52,C_66,D_73] :
      ( m1_subset_1('#skF_2'(A_24,B_52,C_66,D_73),u1_struct_0(B_52))
      | r1_waybel_0(A_24,B_52,C_66)
      | ~ m1_subset_1(D_73,u1_struct_0(B_52))
      | ~ l1_waybel_0(B_52,A_24)
      | v2_struct_0(B_52)
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    ! [B_81,A_77,C_83] :
      ( k3_funct_2(u1_struct_0(B_81),u1_struct_0(A_77),u1_waybel_0(A_77,B_81),C_83) = k2_waybel_0(A_77,B_81,C_83)
      | ~ m1_subset_1(C_83,u1_struct_0(B_81))
      | ~ l1_waybel_0(B_81,A_77)
      | v2_struct_0(B_81)
      | ~ l1_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_140,plain,(
    ! [A_143,B_144,D_145,C_146] :
      ( r2_hidden(k3_funct_2(A_143,B_144,D_145,C_146),k2_relset_1(A_143,B_144,D_145))
      | ~ m1_subset_1(D_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ v1_funct_2(D_145,A_143,B_144)
      | ~ v1_funct_1(D_145)
      | ~ m1_subset_1(C_146,A_143)
      | v1_xboole_0(B_144)
      | v1_xboole_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_240,plain,(
    ! [A_209,B_210,C_211] :
      ( r2_hidden(k2_waybel_0(A_209,B_210,C_211),k2_relset_1(u1_struct_0(B_210),u1_struct_0(A_209),u1_waybel_0(A_209,B_210)))
      | ~ m1_subset_1(u1_waybel_0(A_209,B_210),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_210),u1_struct_0(A_209))))
      | ~ v1_funct_2(u1_waybel_0(A_209,B_210),u1_struct_0(B_210),u1_struct_0(A_209))
      | ~ v1_funct_1(u1_waybel_0(A_209,B_210))
      | ~ m1_subset_1(C_211,u1_struct_0(B_210))
      | v1_xboole_0(u1_struct_0(A_209))
      | v1_xboole_0(u1_struct_0(B_210))
      | ~ m1_subset_1(C_211,u1_struct_0(B_210))
      | ~ l1_waybel_0(B_210,A_209)
      | v2_struct_0(B_210)
      | ~ l1_struct_0(A_209)
      | v2_struct_0(A_209) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_140])).

tff(c_24,plain,(
    ! [A_24,B_52,C_66,D_73] :
      ( ~ r2_hidden(k2_waybel_0(A_24,B_52,'#skF_2'(A_24,B_52,C_66,D_73)),C_66)
      | r1_waybel_0(A_24,B_52,C_66)
      | ~ m1_subset_1(D_73,u1_struct_0(B_52))
      | ~ l1_waybel_0(B_52,A_24)
      | v2_struct_0(B_52)
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_264,plain,(
    ! [A_215,B_216,D_217] :
      ( r1_waybel_0(A_215,B_216,k2_relset_1(u1_struct_0(B_216),u1_struct_0(A_215),u1_waybel_0(A_215,B_216)))
      | ~ m1_subset_1(D_217,u1_struct_0(B_216))
      | ~ m1_subset_1(u1_waybel_0(A_215,B_216),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_216),u1_struct_0(A_215))))
      | ~ v1_funct_2(u1_waybel_0(A_215,B_216),u1_struct_0(B_216),u1_struct_0(A_215))
      | ~ v1_funct_1(u1_waybel_0(A_215,B_216))
      | v1_xboole_0(u1_struct_0(A_215))
      | v1_xboole_0(u1_struct_0(B_216))
      | ~ m1_subset_1('#skF_2'(A_215,B_216,k2_relset_1(u1_struct_0(B_216),u1_struct_0(A_215),u1_waybel_0(A_215,B_216)),D_217),u1_struct_0(B_216))
      | ~ l1_waybel_0(B_216,A_215)
      | v2_struct_0(B_216)
      | ~ l1_struct_0(A_215)
      | v2_struct_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_240,c_24])).

tff(c_274,plain,(
    ! [A_218,B_219,D_220] :
      ( ~ m1_subset_1(u1_waybel_0(A_218,B_219),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_219),u1_struct_0(A_218))))
      | ~ v1_funct_2(u1_waybel_0(A_218,B_219),u1_struct_0(B_219),u1_struct_0(A_218))
      | ~ v1_funct_1(u1_waybel_0(A_218,B_219))
      | v1_xboole_0(u1_struct_0(A_218))
      | v1_xboole_0(u1_struct_0(B_219))
      | r1_waybel_0(A_218,B_219,k2_relset_1(u1_struct_0(B_219),u1_struct_0(A_218),u1_waybel_0(A_218,B_219)))
      | ~ m1_subset_1(D_220,u1_struct_0(B_219))
      | ~ l1_waybel_0(B_219,A_218)
      | v2_struct_0(B_219)
      | ~ l1_struct_0(A_218)
      | v2_struct_0(A_218) ) ),
    inference(resolution,[status(thm)],[c_28,c_264])).

tff(c_282,plain,(
    ! [A_221,B_222,D_223] :
      ( ~ v1_funct_2(u1_waybel_0(A_221,B_222),u1_struct_0(B_222),u1_struct_0(A_221))
      | ~ v1_funct_1(u1_waybel_0(A_221,B_222))
      | v1_xboole_0(u1_struct_0(A_221))
      | v1_xboole_0(u1_struct_0(B_222))
      | r1_waybel_0(A_221,B_222,k2_relset_1(u1_struct_0(B_222),u1_struct_0(A_221),u1_waybel_0(A_221,B_222)))
      | ~ m1_subset_1(D_223,u1_struct_0(B_222))
      | v2_struct_0(B_222)
      | v2_struct_0(A_221)
      | ~ l1_waybel_0(B_222,A_221)
      | ~ l1_struct_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_34,c_274])).

tff(c_301,plain,(
    ! [A_224,B_225] :
      ( ~ v1_funct_2(u1_waybel_0(A_224,B_225),u1_struct_0(B_225),u1_struct_0(A_224))
      | ~ v1_funct_1(u1_waybel_0(A_224,B_225))
      | v1_xboole_0(u1_struct_0(A_224))
      | r1_waybel_0(A_224,B_225,k2_relset_1(u1_struct_0(B_225),u1_struct_0(A_224),u1_waybel_0(A_224,B_225)))
      | v2_struct_0(B_225)
      | v2_struct_0(A_224)
      | ~ l1_waybel_0(B_225,A_224)
      | ~ l1_struct_0(A_224)
      | v1_xboole_0(u1_struct_0(B_225)) ) ),
    inference(resolution,[status(thm)],[c_83,c_282])).

tff(c_40,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',k2_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_306,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_301,c_40])).

tff(c_310,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_306])).

tff(c_311,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_44,c_310])).

tff(c_312,plain,(
    ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_315,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_312])).

tff(c_319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_315])).

tff(c_320,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_322,plain,(
    ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_325,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_322])).

tff(c_329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_325])).

tff(c_330,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_332,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_16,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_339,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_332,c_16])).

tff(c_348,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_339])).

tff(c_351,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_348])).

tff(c_355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_351])).

tff(c_356,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_364,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_356,c_16])).

tff(c_373,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_364])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_373])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:36:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.46  
% 3.04/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.46  %$ v1_funct_2 > r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 3.04/1.46  
% 3.04/1.46  %Foreground sorts:
% 3.04/1.46  
% 3.04/1.46  
% 3.04/1.46  %Background operators:
% 3.04/1.46  
% 3.04/1.46  
% 3.04/1.46  %Foreground operators:
% 3.04/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.04/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.04/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.04/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.04/1.46  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.04/1.46  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 3.04/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.04/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.04/1.46  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 3.04/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.04/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.04/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.04/1.46  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.04/1.46  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 3.04/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.46  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.04/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.04/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.04/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.04/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.04/1.46  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.04/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.04/1.46  
% 3.04/1.48  tff(f_146, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_9)).
% 3.04/1.48  tff(f_122, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 3.04/1.48  tff(f_75, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.04/1.48  tff(f_132, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 3.04/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.04/1.48  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.04/1.48  tff(f_99, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 3.04/1.48  tff(f_115, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (k2_waybel_0(A, B, C) = k3_funct_2(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_waybel_0)).
% 3.04/1.48  tff(f_63, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_funct_2)).
% 3.04/1.48  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.04/1.48  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.04/1.48  tff(c_46, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.04/1.48  tff(c_42, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.04/1.48  tff(c_63, plain, (![B_99, A_100]: (l1_orders_2(B_99) | ~l1_waybel_0(B_99, A_100) | ~l1_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.04/1.48  tff(c_66, plain, (l1_orders_2('#skF_5') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_63])).
% 3.04/1.48  tff(c_69, plain, (l1_orders_2('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_66])).
% 3.04/1.48  tff(c_18, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.04/1.48  tff(c_44, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.04/1.48  tff(c_36, plain, (![A_87, B_88]: (v1_funct_2(u1_waybel_0(A_87, B_88), u1_struct_0(B_88), u1_struct_0(A_87)) | ~l1_waybel_0(B_88, A_87) | ~l1_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.04/1.48  tff(c_38, plain, (![A_87, B_88]: (v1_funct_1(u1_waybel_0(A_87, B_88)) | ~l1_waybel_0(B_88, A_87) | ~l1_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.04/1.48  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.04/1.48  tff(c_75, plain, (![B_103, A_104]: (m1_subset_1(B_103, A_104) | ~r2_hidden(B_103, A_104) | v1_xboole_0(A_104))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.04/1.48  tff(c_83, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_75])).
% 3.04/1.48  tff(c_34, plain, (![A_87, B_88]: (m1_subset_1(u1_waybel_0(A_87, B_88), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_88), u1_struct_0(A_87)))) | ~l1_waybel_0(B_88, A_87) | ~l1_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.04/1.48  tff(c_28, plain, (![A_24, B_52, C_66, D_73]: (m1_subset_1('#skF_2'(A_24, B_52, C_66, D_73), u1_struct_0(B_52)) | r1_waybel_0(A_24, B_52, C_66) | ~m1_subset_1(D_73, u1_struct_0(B_52)) | ~l1_waybel_0(B_52, A_24) | v2_struct_0(B_52) | ~l1_struct_0(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.04/1.48  tff(c_30, plain, (![B_81, A_77, C_83]: (k3_funct_2(u1_struct_0(B_81), u1_struct_0(A_77), u1_waybel_0(A_77, B_81), C_83)=k2_waybel_0(A_77, B_81, C_83) | ~m1_subset_1(C_83, u1_struct_0(B_81)) | ~l1_waybel_0(B_81, A_77) | v2_struct_0(B_81) | ~l1_struct_0(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.04/1.48  tff(c_140, plain, (![A_143, B_144, D_145, C_146]: (r2_hidden(k3_funct_2(A_143, B_144, D_145, C_146), k2_relset_1(A_143, B_144, D_145)) | ~m1_subset_1(D_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~v1_funct_2(D_145, A_143, B_144) | ~v1_funct_1(D_145) | ~m1_subset_1(C_146, A_143) | v1_xboole_0(B_144) | v1_xboole_0(A_143))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.04/1.48  tff(c_240, plain, (![A_209, B_210, C_211]: (r2_hidden(k2_waybel_0(A_209, B_210, C_211), k2_relset_1(u1_struct_0(B_210), u1_struct_0(A_209), u1_waybel_0(A_209, B_210))) | ~m1_subset_1(u1_waybel_0(A_209, B_210), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_210), u1_struct_0(A_209)))) | ~v1_funct_2(u1_waybel_0(A_209, B_210), u1_struct_0(B_210), u1_struct_0(A_209)) | ~v1_funct_1(u1_waybel_0(A_209, B_210)) | ~m1_subset_1(C_211, u1_struct_0(B_210)) | v1_xboole_0(u1_struct_0(A_209)) | v1_xboole_0(u1_struct_0(B_210)) | ~m1_subset_1(C_211, u1_struct_0(B_210)) | ~l1_waybel_0(B_210, A_209) | v2_struct_0(B_210) | ~l1_struct_0(A_209) | v2_struct_0(A_209))), inference(superposition, [status(thm), theory('equality')], [c_30, c_140])).
% 3.04/1.48  tff(c_24, plain, (![A_24, B_52, C_66, D_73]: (~r2_hidden(k2_waybel_0(A_24, B_52, '#skF_2'(A_24, B_52, C_66, D_73)), C_66) | r1_waybel_0(A_24, B_52, C_66) | ~m1_subset_1(D_73, u1_struct_0(B_52)) | ~l1_waybel_0(B_52, A_24) | v2_struct_0(B_52) | ~l1_struct_0(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.04/1.48  tff(c_264, plain, (![A_215, B_216, D_217]: (r1_waybel_0(A_215, B_216, k2_relset_1(u1_struct_0(B_216), u1_struct_0(A_215), u1_waybel_0(A_215, B_216))) | ~m1_subset_1(D_217, u1_struct_0(B_216)) | ~m1_subset_1(u1_waybel_0(A_215, B_216), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_216), u1_struct_0(A_215)))) | ~v1_funct_2(u1_waybel_0(A_215, B_216), u1_struct_0(B_216), u1_struct_0(A_215)) | ~v1_funct_1(u1_waybel_0(A_215, B_216)) | v1_xboole_0(u1_struct_0(A_215)) | v1_xboole_0(u1_struct_0(B_216)) | ~m1_subset_1('#skF_2'(A_215, B_216, k2_relset_1(u1_struct_0(B_216), u1_struct_0(A_215), u1_waybel_0(A_215, B_216)), D_217), u1_struct_0(B_216)) | ~l1_waybel_0(B_216, A_215) | v2_struct_0(B_216) | ~l1_struct_0(A_215) | v2_struct_0(A_215))), inference(resolution, [status(thm)], [c_240, c_24])).
% 3.04/1.48  tff(c_274, plain, (![A_218, B_219, D_220]: (~m1_subset_1(u1_waybel_0(A_218, B_219), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_219), u1_struct_0(A_218)))) | ~v1_funct_2(u1_waybel_0(A_218, B_219), u1_struct_0(B_219), u1_struct_0(A_218)) | ~v1_funct_1(u1_waybel_0(A_218, B_219)) | v1_xboole_0(u1_struct_0(A_218)) | v1_xboole_0(u1_struct_0(B_219)) | r1_waybel_0(A_218, B_219, k2_relset_1(u1_struct_0(B_219), u1_struct_0(A_218), u1_waybel_0(A_218, B_219))) | ~m1_subset_1(D_220, u1_struct_0(B_219)) | ~l1_waybel_0(B_219, A_218) | v2_struct_0(B_219) | ~l1_struct_0(A_218) | v2_struct_0(A_218))), inference(resolution, [status(thm)], [c_28, c_264])).
% 3.04/1.48  tff(c_282, plain, (![A_221, B_222, D_223]: (~v1_funct_2(u1_waybel_0(A_221, B_222), u1_struct_0(B_222), u1_struct_0(A_221)) | ~v1_funct_1(u1_waybel_0(A_221, B_222)) | v1_xboole_0(u1_struct_0(A_221)) | v1_xboole_0(u1_struct_0(B_222)) | r1_waybel_0(A_221, B_222, k2_relset_1(u1_struct_0(B_222), u1_struct_0(A_221), u1_waybel_0(A_221, B_222))) | ~m1_subset_1(D_223, u1_struct_0(B_222)) | v2_struct_0(B_222) | v2_struct_0(A_221) | ~l1_waybel_0(B_222, A_221) | ~l1_struct_0(A_221))), inference(resolution, [status(thm)], [c_34, c_274])).
% 3.04/1.48  tff(c_301, plain, (![A_224, B_225]: (~v1_funct_2(u1_waybel_0(A_224, B_225), u1_struct_0(B_225), u1_struct_0(A_224)) | ~v1_funct_1(u1_waybel_0(A_224, B_225)) | v1_xboole_0(u1_struct_0(A_224)) | r1_waybel_0(A_224, B_225, k2_relset_1(u1_struct_0(B_225), u1_struct_0(A_224), u1_waybel_0(A_224, B_225))) | v2_struct_0(B_225) | v2_struct_0(A_224) | ~l1_waybel_0(B_225, A_224) | ~l1_struct_0(A_224) | v1_xboole_0(u1_struct_0(B_225)))), inference(resolution, [status(thm)], [c_83, c_282])).
% 3.04/1.48  tff(c_40, plain, (~r1_waybel_0('#skF_4', '#skF_5', k2_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.04/1.48  tff(c_306, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_301, c_40])).
% 3.04/1.48  tff(c_310, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_306])).
% 3.04/1.48  tff(c_311, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_48, c_44, c_310])).
% 3.04/1.48  tff(c_312, plain, (~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_311])).
% 3.04/1.48  tff(c_315, plain, (~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_312])).
% 3.04/1.48  tff(c_319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_315])).
% 3.04/1.48  tff(c_320, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_311])).
% 3.04/1.48  tff(c_322, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_320])).
% 3.04/1.48  tff(c_325, plain, (~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_322])).
% 3.04/1.48  tff(c_329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_325])).
% 3.04/1.48  tff(c_330, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_320])).
% 3.04/1.48  tff(c_332, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_330])).
% 3.04/1.48  tff(c_16, plain, (![A_22]: (~v1_xboole_0(u1_struct_0(A_22)) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.04/1.48  tff(c_339, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_332, c_16])).
% 3.04/1.48  tff(c_348, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_339])).
% 3.04/1.48  tff(c_351, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_18, c_348])).
% 3.04/1.48  tff(c_355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_351])).
% 3.04/1.48  tff(c_356, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_330])).
% 3.04/1.48  tff(c_364, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_356, c_16])).
% 3.04/1.48  tff(c_373, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_364])).
% 3.04/1.48  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_373])).
% 3.04/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.48  
% 3.04/1.48  Inference rules
% 3.04/1.48  ----------------------
% 3.04/1.48  #Ref     : 0
% 3.04/1.48  #Sup     : 63
% 3.04/1.48  #Fact    : 0
% 3.04/1.48  #Define  : 0
% 3.04/1.48  #Split   : 3
% 3.04/1.48  #Chain   : 0
% 3.04/1.48  #Close   : 0
% 3.04/1.48  
% 3.04/1.48  Ordering : KBO
% 3.04/1.48  
% 3.04/1.48  Simplification rules
% 3.04/1.48  ----------------------
% 3.04/1.48  #Subsume      : 15
% 3.04/1.48  #Demod        : 9
% 3.04/1.48  #Tautology    : 13
% 3.04/1.48  #SimpNegUnit  : 7
% 3.04/1.48  #BackRed      : 0
% 3.04/1.48  
% 3.04/1.48  #Partial instantiations: 0
% 3.04/1.48  #Strategies tried      : 1
% 3.04/1.48  
% 3.04/1.48  Timing (in seconds)
% 3.04/1.48  ----------------------
% 3.04/1.48  Preprocessing        : 0.31
% 3.04/1.48  Parsing              : 0.17
% 3.04/1.48  CNF conversion       : 0.03
% 3.04/1.48  Main loop            : 0.41
% 3.04/1.48  Inferencing          : 0.17
% 3.04/1.48  Reduction            : 0.08
% 3.04/1.48  Demodulation         : 0.05
% 3.04/1.48  BG Simplification    : 0.02
% 3.04/1.48  Subsumption          : 0.10
% 3.04/1.49  Abstraction          : 0.01
% 3.04/1.49  MUC search           : 0.00
% 3.04/1.49  Cooper               : 0.00
% 3.04/1.49  Total                : 0.76
% 3.04/1.49  Index Insertion      : 0.00
% 3.04/1.49  Index Deletion       : 0.00
% 3.04/1.49  Index Matching       : 0.00
% 3.04/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
